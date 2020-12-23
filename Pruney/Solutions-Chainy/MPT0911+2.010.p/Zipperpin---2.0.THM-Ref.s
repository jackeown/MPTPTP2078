%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AjpA8RTbgf

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:57 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 293 expanded)
%              Number of leaves         :   38 ( 105 expanded)
%              Depth                    :   19
%              Number of atoms          : 1331 (4892 expanded)
%              Number of equality atoms :  163 ( 674 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(t71_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = H ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = H ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( X51 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 )
      | ( X54
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X51 @ X52 @ X53 @ X54 ) @ ( k6_mcart_1 @ X51 @ X52 @ X53 @ X54 ) @ ( k7_mcart_1 @ X51 @ X52 @ X53 @ X54 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k3_zfmisc_1 @ X51 @ X52 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_E_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('8',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X55 @ X56 @ X58 @ X57 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X57 ) ) )
      | ~ ( m1_subset_1 @ X57 @ ( k3_zfmisc_1 @ X55 @ X56 @ X58 ) )
      | ( X58 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('9',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X55 @ X56 @ X58 @ X57 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X57 ) ) )
      | ~ ( m1_subset_1 @ X57 @ ( k3_zfmisc_1 @ X55 @ X56 @ X58 ) )
      | ( X58 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X55 @ X56 @ X58 @ X57 )
        = ( k2_mcart_1 @ X57 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k3_zfmisc_1 @ X55 @ X56 @ X58 ) )
      | ( X58 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('23',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k2_mcart_1 @ sk_E_2 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( sk_E_2
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['6','13','20','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('32',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('33',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X48 ) @ X49 )
      | ~ ( r2_hidden @ X48 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X48 ) @ X50 )
      | ~ ( r2_hidden @ X48 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('38',plain,(
    ! [X64: $i] :
      ( ( X64 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X64 ) @ X64 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('42',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X59: $i,X60: $i,X61: $i,X63: $i] :
      ( ( X61 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X63 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('45',plain,(
    ! [X59: $i,X60: $i,X63: $i] :
      ( ( k4_zfmisc_1 @ X59 @ X60 @ k1_xboole_0 @ X63 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('47',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X59: $i,X60: $i,X61: $i,X63: $i] :
      ( ( X63 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X63 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('55',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['43','56'])).

thf('58',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['60','61','62','63'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('65',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('67',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('68',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('73',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('74',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X70 @ sk_B_2 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X71 @ X70 @ X72 ) )
      | ( sk_D_2 = X72 )
      | ~ ( m1_subset_1 @ X72 @ sk_C )
      | ~ ( m1_subset_1 @ X71 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_2 = X1 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ( sk_D_2
      = ( k2_mcart_1 @ sk_E_2 ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('82',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X44 @ X45 @ X46 @ X47 ) @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k3_zfmisc_1 @ X44 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('83',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26'])).

thf('85',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('87',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X48 ) @ X49 )
      | ~ ( r2_hidden @ X48 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('90',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','70'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('107',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ( sk_D_2
      = ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['80','85','107'])).

thf('109',plain,
    ( sk_D_2
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26'])).

thf('112',plain,(
    sk_D_2
 != ( k2_mcart_1 @ sk_E_2 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['109','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AjpA8RTbgf
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 991 iterations in 0.714s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.14  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.90/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.14  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.14  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.90/1.14  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.14  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.90/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.14  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.14  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.14  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.90/1.14  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.14  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.90/1.14  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.90/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.14  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.90/1.14  thf(t71_mcart_1, conjecture,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.14       ( ( ![F:$i]:
% 0.90/1.14           ( ( m1_subset_1 @ F @ A ) =>
% 0.90/1.14             ( ![G:$i]:
% 0.90/1.14               ( ( m1_subset_1 @ G @ B ) =>
% 0.90/1.14                 ( ![H:$i]:
% 0.90/1.14                   ( ( m1_subset_1 @ H @ C ) =>
% 0.90/1.14                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.90/1.14                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.90/1.14         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.14        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.14          ( ( ![F:$i]:
% 0.90/1.14              ( ( m1_subset_1 @ F @ A ) =>
% 0.90/1.14                ( ![G:$i]:
% 0.90/1.14                  ( ( m1_subset_1 @ G @ B ) =>
% 0.90/1.14                    ( ![H:$i]:
% 0.90/1.14                      ( ( m1_subset_1 @ H @ C ) =>
% 0.90/1.14                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.90/1.14                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.90/1.14            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.90/1.14  thf('0', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t48_mcart_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.14          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.90/1.14          ( ~( ![D:$i]:
% 0.90/1.14               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.14                 ( ( D ) =
% 0.90/1.14                   ( k3_mcart_1 @
% 0.90/1.14                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.90/1.14                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.90/1.14                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('1', plain,
% 0.90/1.14      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.90/1.14         (((X51) = (k1_xboole_0))
% 0.90/1.14          | ((X52) = (k1_xboole_0))
% 0.90/1.14          | ((X54)
% 0.90/1.14              = (k3_mcart_1 @ (k5_mcart_1 @ X51 @ X52 @ X53 @ X54) @ 
% 0.90/1.14                 (k6_mcart_1 @ X51 @ X52 @ X53 @ X54) @ 
% 0.90/1.14                 (k7_mcart_1 @ X51 @ X52 @ X53 @ X54)))
% 0.90/1.14          | ~ (m1_subset_1 @ X54 @ (k3_zfmisc_1 @ X51 @ X52 @ X53))
% 0.90/1.14          | ((X53) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.90/1.14  thf('2', plain,
% 0.90/1.14      ((((sk_C) = (k1_xboole_0))
% 0.90/1.14        | ((sk_E_2)
% 0.90/1.14            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ 
% 0.90/1.14               (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ 
% 0.90/1.14               (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)))
% 0.90/1.14        | ((sk_B_2) = (k1_xboole_0))
% 0.90/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('4', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('6', plain,
% 0.90/1.14      (((sk_E_2)
% 0.90/1.14         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ 
% 0.90/1.14            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ 
% 0.90/1.14            (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.90/1.14  thf('7', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t50_mcart_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.14          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.90/1.14          ( ~( ![D:$i]:
% 0.90/1.14               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.14                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.90/1.14                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.90/1.14                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.90/1.14                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.90/1.14                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('8', plain,
% 0.90/1.14      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.90/1.14         (((X55) = (k1_xboole_0))
% 0.90/1.14          | ((X56) = (k1_xboole_0))
% 0.90/1.14          | ((k5_mcart_1 @ X55 @ X56 @ X58 @ X57)
% 0.90/1.14              = (k1_mcart_1 @ (k1_mcart_1 @ X57)))
% 0.90/1.14          | ~ (m1_subset_1 @ X57 @ (k3_zfmisc_1 @ X55 @ X56 @ X58))
% 0.90/1.14          | ((X58) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.90/1.14  thf('9', plain,
% 0.90/1.14      ((((sk_C) = (k1_xboole_0))
% 0.90/1.14        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.90/1.14            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))
% 0.90/1.14        | ((sk_B_2) = (k1_xboole_0))
% 0.90/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.14  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('11', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('12', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('13', plain,
% 0.90/1.14      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.90/1.14         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 0.90/1.14  thf('14', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('15', plain,
% 0.90/1.14      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.90/1.14         (((X55) = (k1_xboole_0))
% 0.90/1.14          | ((X56) = (k1_xboole_0))
% 0.90/1.14          | ((k6_mcart_1 @ X55 @ X56 @ X58 @ X57)
% 0.90/1.14              = (k2_mcart_1 @ (k1_mcart_1 @ X57)))
% 0.90/1.14          | ~ (m1_subset_1 @ X57 @ (k3_zfmisc_1 @ X55 @ X56 @ X58))
% 0.90/1.14          | ((X58) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      ((((sk_C) = (k1_xboole_0))
% 0.90/1.14        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.90/1.14            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))
% 0.90/1.14        | ((sk_B_2) = (k1_xboole_0))
% 0.90/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('18', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('19', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('20', plain,
% 0.90/1.14      (((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.90/1.14         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['16', '17', '18', '19'])).
% 0.90/1.14  thf('21', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('22', plain,
% 0.90/1.14      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.90/1.14         (((X55) = (k1_xboole_0))
% 0.90/1.14          | ((X56) = (k1_xboole_0))
% 0.90/1.14          | ((k7_mcart_1 @ X55 @ X56 @ X58 @ X57) = (k2_mcart_1 @ X57))
% 0.90/1.14          | ~ (m1_subset_1 @ X57 @ (k3_zfmisc_1 @ X55 @ X56 @ X58))
% 0.90/1.14          | ((X58) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      ((((sk_C) = (k1_xboole_0))
% 0.90/1.14        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))
% 0.90/1.14        | ((sk_B_2) = (k1_xboole_0))
% 0.90/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.14  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('25', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('26', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['23', '24', '25', '26'])).
% 0.90/1.14  thf('28', plain,
% 0.90/1.14      (((sk_E_2)
% 0.90/1.14         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.90/1.14            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ (k2_mcart_1 @ sk_E_2)))),
% 0.90/1.14      inference('demod', [status(thm)], ['6', '13', '20', '27'])).
% 0.90/1.14  thf('29', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t2_subset, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ A @ B ) =>
% 0.90/1.14       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.90/1.14  thf('30', plain,
% 0.90/1.14      (![X30 : $i, X31 : $i]:
% 0.90/1.14         ((r2_hidden @ X30 @ X31)
% 0.90/1.14          | (v1_xboole_0 @ X31)
% 0.90/1.14          | ~ (m1_subset_1 @ X30 @ X31))),
% 0.90/1.14      inference('cnf', [status(esa)], [t2_subset])).
% 0.90/1.14  thf('31', plain,
% 0.90/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.90/1.14        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.14  thf(d3_zfmisc_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.90/1.14       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.90/1.14  thf('32', plain,
% 0.90/1.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.14         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 0.90/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.90/1.14  thf(t10_mcart_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.90/1.14       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.90/1.14         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.90/1.14         ((r2_hidden @ (k1_mcart_1 @ X48) @ X49)
% 0.90/1.14          | ~ (r2_hidden @ X48 @ (k2_zfmisc_1 @ X49 @ X50)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.90/1.14  thf('34', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.90/1.14          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['32', '33'])).
% 0.90/1.14  thf('35', plain,
% 0.90/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.90/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['31', '34'])).
% 0.90/1.14  thf('36', plain,
% 0.90/1.14      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.90/1.14         ((r2_hidden @ (k2_mcart_1 @ X48) @ X50)
% 0.90/1.14          | ~ (r2_hidden @ X48 @ (k2_zfmisc_1 @ X49 @ X50)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.90/1.14  thf('37', plain,
% 0.90/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.90/1.14        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 0.90/1.14      inference('sup-', [status(thm)], ['35', '36'])).
% 0.90/1.14  thf(t6_mcart_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.90/1.14          ( ![B:$i]:
% 0.90/1.14            ( ~( ( r2_hidden @ B @ A ) & 
% 0.90/1.14                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.90/1.14                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.90/1.14                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.90/1.14                       ( r2_hidden @ G @ B ) ) =>
% 0.90/1.14                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('38', plain,
% 0.90/1.14      (![X64 : $i]:
% 0.90/1.14         (((X64) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X64) @ X64))),
% 0.90/1.14      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.90/1.14  thf(d1_xboole_0, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.90/1.14  thf('39', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.14  thf('40', plain,
% 0.90/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.14  thf('41', plain,
% 0.90/1.14      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2)
% 0.90/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['37', '40'])).
% 0.90/1.14  thf(d4_zfmisc_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.90/1.14       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.90/1.14  thf('42', plain,
% 0.90/1.14      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.14         ((k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43)
% 0.90/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X40 @ X41 @ X42) @ X43))),
% 0.90/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.90/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.90/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 0.90/1.14      inference('sup+', [status(thm)], ['41', '42'])).
% 0.90/1.14  thf(t55_mcart_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.14         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.90/1.14       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      (![X59 : $i, X60 : $i, X61 : $i, X63 : $i]:
% 0.90/1.14         (((X61) != (k1_xboole_0))
% 0.90/1.14          | ((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X63) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.90/1.14  thf('45', plain,
% 0.90/1.14      (![X59 : $i, X60 : $i, X63 : $i]:
% 0.90/1.14         ((k4_zfmisc_1 @ X59 @ X60 @ k1_xboole_0 @ X63) = (k1_xboole_0))),
% 0.90/1.14      inference('simplify', [status(thm)], ['44'])).
% 0.90/1.14  thf('46', plain,
% 0.90/1.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.14         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 0.90/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.90/1.14  thf('47', plain,
% 0.90/1.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.14         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 0.90/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.90/1.14  thf('48', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.90/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.90/1.14      inference('sup+', [status(thm)], ['46', '47'])).
% 0.90/1.14  thf('49', plain,
% 0.90/1.14      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.14         ((k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43)
% 0.90/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X40 @ X41 @ X42) @ X43))),
% 0.90/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.90/1.14           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.90/1.14      inference('demod', [status(thm)], ['48', '49'])).
% 0.90/1.14  thf('51', plain,
% 0.90/1.14      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.14         ((k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43)
% 0.90/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X40 @ X41 @ X42) @ X43))),
% 0.90/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.90/1.14  thf('52', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.14         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 0.90/1.14           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.90/1.14      inference('sup+', [status(thm)], ['50', '51'])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         ((k1_xboole_0)
% 0.90/1.14           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['45', '52'])).
% 0.90/1.14  thf('54', plain,
% 0.90/1.14      (![X59 : $i, X60 : $i, X61 : $i, X63 : $i]:
% 0.90/1.14         (((X63) != (k1_xboole_0))
% 0.90/1.14          | ((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X63) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.90/1.14  thf('55', plain,
% 0.90/1.14      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.90/1.14         ((k4_zfmisc_1 @ X59 @ X60 @ X61 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.14      inference('simplify', [status(thm)], ['54'])).
% 0.90/1.14  thf('56', plain,
% 0.90/1.14      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['53', '55'])).
% 0.90/1.14  thf('57', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.90/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 0.90/1.14      inference('demod', [status(thm)], ['43', '56'])).
% 0.90/1.14  thf('58', plain,
% 0.90/1.14      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.90/1.14         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 0.90/1.14          | ((X62) = (k1_xboole_0))
% 0.90/1.14          | ((X61) = (k1_xboole_0))
% 0.90/1.14          | ((X60) = (k1_xboole_0))
% 0.90/1.14          | ((X59) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.90/1.14  thf('59', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2)
% 0.90/1.14          | ((sk_A) = (k1_xboole_0))
% 0.90/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.90/1.14          | ((sk_C) = (k1_xboole_0))
% 0.90/1.14          | ((X0) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['57', '58'])).
% 0.90/1.14  thf('60', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((X0) = (k1_xboole_0))
% 0.90/1.14          | ((sk_C) = (k1_xboole_0))
% 0.90/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.90/1.14          | ((sk_A) = (k1_xboole_0))
% 0.90/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 0.90/1.14      inference('simplify', [status(thm)], ['59'])).
% 0.90/1.14  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('62', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('63', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('64', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((X0) = (k1_xboole_0))
% 0.90/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['60', '61', '62', '63'])).
% 0.90/1.14  thf(t1_subset, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.90/1.14  thf('65', plain,
% 0.90/1.14      (![X28 : $i, X29 : $i]:
% 0.90/1.14         ((m1_subset_1 @ X28 @ X29) | ~ (r2_hidden @ X28 @ X29))),
% 0.90/1.14      inference('cnf', [status(esa)], [t1_subset])).
% 0.90/1.14  thf('66', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((X0) = (k1_xboole_0))
% 0.90/1.14          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 0.90/1.14      inference('sup-', [status(thm)], ['64', '65'])).
% 0.90/1.14  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.90/1.14  thf('67', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.90/1.14      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.14  thf('68', plain,
% 0.90/1.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.90/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.14  thf(t7_ordinal1, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.14  thf('69', plain,
% 0.90/1.14      (![X32 : $i, X33 : $i]:
% 0.90/1.14         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.90/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.90/1.14  thf('70', plain,
% 0.90/1.14      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['68', '69'])).
% 0.90/1.14  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.14      inference('sup-', [status(thm)], ['67', '70'])).
% 0.90/1.14  thf('72', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v1_xboole_0 @ X0)
% 0.90/1.14          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 0.90/1.14      inference('sup+', [status(thm)], ['66', '71'])).
% 0.90/1.14  thf(d2_tarski, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.90/1.14  thf('73', plain,
% 0.90/1.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.14         (((X5) != (X4))
% 0.90/1.14          | (r2_hidden @ X5 @ X6)
% 0.90/1.14          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.90/1.14      inference('cnf', [status(esa)], [d2_tarski])).
% 0.90/1.14  thf('74', plain,
% 0.90/1.14      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.90/1.14      inference('simplify', [status(thm)], ['73'])).
% 0.90/1.14  thf('75', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.14  thf('76', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['74', '75'])).
% 0.90/1.14  thf('77', plain,
% 0.90/1.14      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2)),
% 0.90/1.14      inference('sup-', [status(thm)], ['72', '76'])).
% 0.90/1.14  thf('78', plain,
% 0.90/1.14      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X70 @ sk_B_2)
% 0.90/1.14          | ((sk_E_2) != (k3_mcart_1 @ X71 @ X70 @ X72))
% 0.90/1.14          | ((sk_D_2) = (X72))
% 0.90/1.14          | ~ (m1_subset_1 @ X72 @ sk_C)
% 0.90/1.14          | ~ (m1_subset_1 @ X71 @ sk_A))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.90/1.14          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.90/1.14          | ((sk_D_2) = (X1))
% 0.90/1.14          | ((sk_E_2)
% 0.90/1.14              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X1)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['77', '78'])).
% 0.90/1.14  thf('80', plain,
% 0.90/1.14      ((((sk_E_2) != (sk_E_2))
% 0.90/1.14        | ((sk_D_2) = (k2_mcart_1 @ sk_E_2))
% 0.90/1.14        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C)
% 0.90/1.14        | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['28', '79'])).
% 0.90/1.14  thf('81', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(dt_k7_mcart_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.14       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.90/1.14  thf('82', plain,
% 0.90/1.14      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.14         ((m1_subset_1 @ (k7_mcart_1 @ X44 @ X45 @ X46 @ X47) @ X46)
% 0.90/1.14          | ~ (m1_subset_1 @ X47 @ (k3_zfmisc_1 @ X44 @ X45 @ X46)))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.90/1.14  thf('83', plain,
% 0.90/1.14      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.14  thf('84', plain,
% 0.90/1.14      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['23', '24', '25', '26'])).
% 0.90/1.14  thf('85', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['83', '84'])).
% 0.90/1.14  thf('86', plain,
% 0.90/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.90/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['31', '34'])).
% 0.90/1.14  thf('87', plain,
% 0.90/1.14      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.90/1.14         ((r2_hidden @ (k1_mcart_1 @ X48) @ X49)
% 0.90/1.14          | ~ (r2_hidden @ X48 @ (k2_zfmisc_1 @ X49 @ X50)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.90/1.14  thf('88', plain,
% 0.90/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.90/1.14        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['86', '87'])).
% 0.90/1.14  thf('89', plain,
% 0.90/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.14  thf('90', plain,
% 0.90/1.14      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)
% 0.90/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['88', '89'])).
% 0.90/1.14  thf('91', plain,
% 0.90/1.14      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.14         ((k4_zfmisc_1 @ X40 @ X41 @ X42 @ X43)
% 0.90/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X40 @ X41 @ X42) @ X43))),
% 0.90/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.90/1.14  thf('92', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.90/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.90/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.90/1.14      inference('sup+', [status(thm)], ['90', '91'])).
% 0.90/1.14  thf('93', plain,
% 0.90/1.14      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['53', '55'])).
% 0.90/1.14  thf('94', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.90/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['92', '93'])).
% 0.90/1.14  thf('95', plain,
% 0.90/1.14      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.90/1.14         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 0.90/1.14          | ((X62) = (k1_xboole_0))
% 0.90/1.14          | ((X61) = (k1_xboole_0))
% 0.90/1.14          | ((X60) = (k1_xboole_0))
% 0.90/1.14          | ((X59) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.90/1.14  thf('96', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)
% 0.90/1.14          | ((sk_A) = (k1_xboole_0))
% 0.90/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.90/1.14          | ((sk_C) = (k1_xboole_0))
% 0.90/1.14          | ((X0) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['94', '95'])).
% 0.90/1.14  thf('97', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((X0) = (k1_xboole_0))
% 0.90/1.14          | ((sk_C) = (k1_xboole_0))
% 0.90/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.90/1.14          | ((sk_A) = (k1_xboole_0))
% 0.90/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.90/1.14      inference('simplify', [status(thm)], ['96'])).
% 0.90/1.14  thf('98', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('99', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('100', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('101', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((X0) = (k1_xboole_0))
% 0.90/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['97', '98', '99', '100'])).
% 0.90/1.14  thf('102', plain,
% 0.90/1.14      (![X28 : $i, X29 : $i]:
% 0.90/1.14         ((m1_subset_1 @ X28 @ X29) | ~ (r2_hidden @ X28 @ X29))),
% 0.90/1.14      inference('cnf', [status(esa)], [t1_subset])).
% 0.90/1.14  thf('103', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((X0) = (k1_xboole_0))
% 0.90/1.14          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['101', '102'])).
% 0.90/1.14  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.14      inference('sup-', [status(thm)], ['67', '70'])).
% 0.90/1.14  thf('105', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v1_xboole_0 @ X0)
% 0.90/1.14          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.90/1.14      inference('sup+', [status(thm)], ['103', '104'])).
% 0.90/1.14  thf('106', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['74', '75'])).
% 0.90/1.14  thf('107', plain,
% 0.90/1.14      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)),
% 0.90/1.14      inference('sup-', [status(thm)], ['105', '106'])).
% 0.90/1.14  thf('108', plain,
% 0.90/1.14      ((((sk_E_2) != (sk_E_2)) | ((sk_D_2) = (k2_mcart_1 @ sk_E_2)))),
% 0.90/1.14      inference('demod', [status(thm)], ['80', '85', '107'])).
% 0.90/1.14  thf('109', plain, (((sk_D_2) = (k2_mcart_1 @ sk_E_2))),
% 0.90/1.14      inference('simplify', [status(thm)], ['108'])).
% 0.90/1.14  thf('110', plain,
% 0.90/1.14      (((sk_D_2) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('111', plain,
% 0.90/1.14      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['23', '24', '25', '26'])).
% 0.90/1.14  thf('112', plain, (((sk_D_2) != (k2_mcart_1 @ sk_E_2))),
% 0.90/1.14      inference('demod', [status(thm)], ['110', '111'])).
% 0.90/1.14  thf('113', plain, ($false),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['109', '112'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
