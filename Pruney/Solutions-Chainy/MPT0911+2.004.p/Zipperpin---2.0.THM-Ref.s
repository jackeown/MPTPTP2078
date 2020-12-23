%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DDNTtEA4q6

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:56 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 247 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :   17
%              Number of atoms          : 1166 (3777 expanded)
%              Number of equality atoms :  154 ( 489 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ X39 )
      | ( r2_hidden @ X38 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X52
        = ( k4_tarski @ ( k1_mcart_1 @ X52 ) @ ( k2_mcart_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_zfmisc_1 @ X46 @ X47 @ X48 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X41: $i,X42: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('9',plain,(
    ! [X54: $i] :
      ( ( X54 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X54 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k3_zfmisc_1 @ X59 @ X60 @ X61 )
       != k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_E_2
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_zfmisc_1 @ X46 @ X47 @ X48 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('22',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X52
        = ( k4_tarski @ ( k1_mcart_1 @ X52 ) @ ( k2_mcart_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X41: $i,X42: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('30',plain,
    ( ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k3_zfmisc_1 @ X59 @ X60 @ X61 )
       != k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_mcart_1 @ sk_E_2 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34','35','36'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('38',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k3_mcart_1 @ X43 @ X44 @ X45 )
      = ( k4_tarski @ ( k4_tarski @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('41',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X49 ) @ X51 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('44',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k3_zfmisc_1 @ X59 @ X60 @ X61 )
       != k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( m1_subset_1 @ X38 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ sk_B_2 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X68 @ X67 @ X69 ) )
      | ( sk_D_2 = X69 )
      | ~ ( m1_subset_1 @ X69 @ sk_C )
      | ~ ( m1_subset_1 @ X68 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_2 = X1 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('60',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('63',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k3_zfmisc_1 @ X59 @ X60 @ X61 )
       != k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('72',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','72'])).

thf('74',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C )
    | ( sk_D_2
      = ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['19','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('76',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_zfmisc_1 @ X46 @ X47 @ X48 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('77',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X49 ) @ X51 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('81',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k3_zfmisc_1 @ X59 @ X60 @ X61 )
       != k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ( sk_D_2
      = ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['74','90'])).

thf('92',plain,
    ( sk_D_2
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( X63 = k1_xboole_0 )
      | ( X64 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X63 @ X64 @ X66 @ X65 )
        = ( k2_mcart_1 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k3_zfmisc_1 @ X63 @ X64 @ X66 ) )
      | ( X66 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('96',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k2_mcart_1 @ sk_E_2 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    sk_D_2
 != ( k2_mcart_1 @ sk_E_2 ) ),
    inference(demod,[status(thm)],['93','100'])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DDNTtEA4q6
% 0.14/0.37  % Computer   : n015.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 12:20:53 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.29/1.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.29/1.54  % Solved by: fo/fo7.sh
% 1.29/1.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.54  % done 2248 iterations in 1.055s
% 1.29/1.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.29/1.54  % SZS output start Refutation
% 1.29/1.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.29/1.54  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.29/1.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.54  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.29/1.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.29/1.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.29/1.54  thf(sk_E_2_type, type, sk_E_2: $i).
% 1.29/1.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.29/1.54  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.29/1.54  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.29/1.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.29/1.54  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.29/1.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.29/1.54  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.29/1.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.29/1.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.29/1.54  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 1.29/1.54  thf(sk_C_type, type, sk_C: $i).
% 1.29/1.54  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.29/1.54  thf(t71_mcart_1, conjecture,
% 1.29/1.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.29/1.54     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.29/1.54       ( ( ![F:$i]:
% 1.29/1.54           ( ( m1_subset_1 @ F @ A ) =>
% 1.29/1.54             ( ![G:$i]:
% 1.29/1.54               ( ( m1_subset_1 @ G @ B ) =>
% 1.29/1.54                 ( ![H:$i]:
% 1.29/1.54                   ( ( m1_subset_1 @ H @ C ) =>
% 1.29/1.54                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.29/1.54                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.29/1.54         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.29/1.54           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.29/1.54           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.29/1.54  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.29/1.54        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.29/1.54          ( ( ![F:$i]:
% 1.29/1.54              ( ( m1_subset_1 @ F @ A ) =>
% 1.29/1.54                ( ![G:$i]:
% 1.29/1.54                  ( ( m1_subset_1 @ G @ B ) =>
% 1.29/1.54                    ( ![H:$i]:
% 1.29/1.54                      ( ( m1_subset_1 @ H @ C ) =>
% 1.29/1.54                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.29/1.54                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.29/1.54            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.29/1.54              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.29/1.54              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.29/1.54    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 1.29/1.54  thf('0', plain,
% 1.29/1.54      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf(d2_subset_1, axiom,
% 1.29/1.54    (![A:$i,B:$i]:
% 1.29/1.54     ( ( ( v1_xboole_0 @ A ) =>
% 1.29/1.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.29/1.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.29/1.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.29/1.54  thf('1', plain,
% 1.29/1.54      (![X38 : $i, X39 : $i]:
% 1.29/1.54         (~ (m1_subset_1 @ X38 @ X39)
% 1.29/1.54          | (r2_hidden @ X38 @ X39)
% 1.29/1.54          | (v1_xboole_0 @ X39))),
% 1.29/1.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.29/1.54  thf('2', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['0', '1'])).
% 1.29/1.54  thf(t23_mcart_1, axiom,
% 1.29/1.54    (![A:$i,B:$i]:
% 1.29/1.54     ( ( v1_relat_1 @ B ) =>
% 1.29/1.54       ( ( r2_hidden @ A @ B ) =>
% 1.29/1.54         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 1.29/1.54  thf('3', plain,
% 1.29/1.54      (![X52 : $i, X53 : $i]:
% 1.29/1.54         (((X52) = (k4_tarski @ (k1_mcart_1 @ X52) @ (k2_mcart_1 @ X52)))
% 1.29/1.54          | ~ (v1_relat_1 @ X53)
% 1.29/1.54          | ~ (r2_hidden @ X52 @ X53))),
% 1.29/1.54      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.29/1.54  thf('4', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | ((sk_E_2)
% 1.29/1.54            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 1.29/1.54      inference('sup-', [status(thm)], ['2', '3'])).
% 1.29/1.54  thf(d3_zfmisc_1, axiom,
% 1.29/1.54    (![A:$i,B:$i,C:$i]:
% 1.29/1.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.29/1.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.29/1.54  thf('5', plain,
% 1.29/1.54      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.29/1.54         ((k3_zfmisc_1 @ X46 @ X47 @ X48)
% 1.29/1.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47) @ X48))),
% 1.29/1.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.29/1.54  thf(fc6_relat_1, axiom,
% 1.29/1.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.29/1.54  thf('6', plain,
% 1.29/1.54      (![X41 : $i, X42 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X41 @ X42))),
% 1.29/1.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.29/1.54  thf('7', plain,
% 1.29/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.54         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 1.29/1.54      inference('sup+', [status(thm)], ['5', '6'])).
% 1.29/1.54  thf('8', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | ((sk_E_2)
% 1.29/1.54            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 1.29/1.54      inference('demod', [status(thm)], ['4', '7'])).
% 1.29/1.54  thf(t34_mcart_1, axiom,
% 1.29/1.54    (![A:$i]:
% 1.29/1.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.29/1.54          ( ![B:$i]:
% 1.29/1.54            ( ~( ( r2_hidden @ B @ A ) & 
% 1.29/1.54                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 1.29/1.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.29/1.54                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 1.29/1.54  thf('9', plain,
% 1.29/1.54      (![X54 : $i]:
% 1.29/1.54         (((X54) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X54) @ X54))),
% 1.29/1.54      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.29/1.54  thf(d1_xboole_0, axiom,
% 1.29/1.54    (![A:$i]:
% 1.29/1.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.29/1.54  thf('10', plain,
% 1.29/1.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.29/1.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.29/1.54  thf('11', plain,
% 1.29/1.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.29/1.54      inference('sup-', [status(thm)], ['9', '10'])).
% 1.29/1.54  thf('12', plain,
% 1.29/1.54      ((((sk_E_2) = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))
% 1.29/1.54        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['8', '11'])).
% 1.29/1.54  thf(t35_mcart_1, axiom,
% 1.29/1.54    (![A:$i,B:$i,C:$i]:
% 1.29/1.54     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.29/1.54         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 1.29/1.54       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 1.29/1.54  thf('13', plain,
% 1.29/1.54      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.29/1.54         (((k3_zfmisc_1 @ X59 @ X60 @ X61) != (k1_xboole_0))
% 1.29/1.54          | ((X61) = (k1_xboole_0))
% 1.29/1.54          | ((X60) = (k1_xboole_0))
% 1.29/1.54          | ((X59) = (k1_xboole_0)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.29/1.54  thf('14', plain,
% 1.29/1.54      ((((k1_xboole_0) != (k1_xboole_0))
% 1.29/1.54        | ((sk_E_2)
% 1.29/1.54            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['12', '13'])).
% 1.29/1.54  thf('15', plain,
% 1.29/1.54      ((((sk_C) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | ((sk_E_2)
% 1.29/1.54            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 1.29/1.54      inference('simplify', [status(thm)], ['14'])).
% 1.29/1.54  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('17', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('19', plain,
% 1.29/1.54      (((sk_E_2) = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))),
% 1.29/1.54      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 1.29/1.54  thf('20', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['0', '1'])).
% 1.29/1.54  thf('21', plain,
% 1.29/1.54      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.29/1.54         ((k3_zfmisc_1 @ X46 @ X47 @ X48)
% 1.29/1.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47) @ X48))),
% 1.29/1.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.29/1.54  thf(t10_mcart_1, axiom,
% 1.29/1.54    (![A:$i,B:$i,C:$i]:
% 1.29/1.54     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.29/1.54       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.29/1.54         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.29/1.54  thf('22', plain,
% 1.29/1.54      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.29/1.54         ((r2_hidden @ (k1_mcart_1 @ X49) @ X50)
% 1.29/1.54          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ X50 @ X51)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.29/1.54  thf('23', plain,
% 1.29/1.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.29/1.54         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.29/1.54          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['21', '22'])).
% 1.29/1.54  thf('24', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['20', '23'])).
% 1.29/1.54  thf('25', plain,
% 1.29/1.54      (![X52 : $i, X53 : $i]:
% 1.29/1.54         (((X52) = (k4_tarski @ (k1_mcart_1 @ X52) @ (k2_mcart_1 @ X52)))
% 1.29/1.54          | ~ (v1_relat_1 @ X53)
% 1.29/1.54          | ~ (r2_hidden @ X52 @ X53))),
% 1.29/1.54      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.29/1.54  thf('26', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 1.29/1.54        | ((k1_mcart_1 @ sk_E_2)
% 1.29/1.54            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 1.29/1.54               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 1.29/1.54      inference('sup-', [status(thm)], ['24', '25'])).
% 1.29/1.54  thf('27', plain,
% 1.29/1.54      (![X41 : $i, X42 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X41 @ X42))),
% 1.29/1.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.29/1.54  thf('28', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | ((k1_mcart_1 @ sk_E_2)
% 1.29/1.54            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 1.29/1.54               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 1.29/1.54      inference('demod', [status(thm)], ['26', '27'])).
% 1.29/1.54  thf('29', plain,
% 1.29/1.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.29/1.54      inference('sup-', [status(thm)], ['9', '10'])).
% 1.29/1.54  thf('30', plain,
% 1.29/1.54      ((((k1_mcart_1 @ sk_E_2)
% 1.29/1.54          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 1.29/1.54             (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))
% 1.29/1.54        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['28', '29'])).
% 1.29/1.54  thf('31', plain,
% 1.29/1.54      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.29/1.54         (((k3_zfmisc_1 @ X59 @ X60 @ X61) != (k1_xboole_0))
% 1.29/1.54          | ((X61) = (k1_xboole_0))
% 1.29/1.54          | ((X60) = (k1_xboole_0))
% 1.29/1.54          | ((X59) = (k1_xboole_0)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.29/1.54  thf('32', plain,
% 1.29/1.54      ((((k1_xboole_0) != (k1_xboole_0))
% 1.29/1.54        | ((k1_mcart_1 @ sk_E_2)
% 1.29/1.54            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 1.29/1.54               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['30', '31'])).
% 1.29/1.54  thf('33', plain,
% 1.29/1.54      ((((sk_C) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | ((k1_mcart_1 @ sk_E_2)
% 1.29/1.54            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 1.29/1.54               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 1.29/1.54      inference('simplify', [status(thm)], ['32'])).
% 1.29/1.54  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('35', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('36', plain, (((sk_C) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('37', plain,
% 1.29/1.54      (((k1_mcart_1 @ sk_E_2)
% 1.29/1.54         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 1.29/1.54            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))),
% 1.29/1.54      inference('simplify_reflect-', [status(thm)], ['33', '34', '35', '36'])).
% 1.29/1.54  thf(d3_mcart_1, axiom,
% 1.29/1.54    (![A:$i,B:$i,C:$i]:
% 1.29/1.54     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.29/1.54  thf('38', plain,
% 1.29/1.54      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.29/1.54         ((k3_mcart_1 @ X43 @ X44 @ X45)
% 1.29/1.54           = (k4_tarski @ (k4_tarski @ X43 @ X44) @ X45))),
% 1.29/1.54      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.29/1.54  thf('39', plain,
% 1.29/1.54      (![X0 : $i]:
% 1.29/1.54         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 1.29/1.54           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X0)
% 1.29/1.54           = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))),
% 1.29/1.54      inference('sup+', [status(thm)], ['37', '38'])).
% 1.29/1.54  thf('40', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['20', '23'])).
% 1.29/1.54  thf('41', plain,
% 1.29/1.54      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.29/1.54         ((r2_hidden @ (k2_mcart_1 @ X49) @ X51)
% 1.29/1.54          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ X50 @ X51)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.29/1.54  thf('42', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 1.29/1.54      inference('sup-', [status(thm)], ['40', '41'])).
% 1.29/1.54  thf('43', plain,
% 1.29/1.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.29/1.54      inference('sup-', [status(thm)], ['9', '10'])).
% 1.29/1.54  thf('44', plain,
% 1.29/1.54      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2)
% 1.29/1.54        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['42', '43'])).
% 1.29/1.54  thf('45', plain,
% 1.29/1.54      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.29/1.54         (((k3_zfmisc_1 @ X59 @ X60 @ X61) != (k1_xboole_0))
% 1.29/1.54          | ((X61) = (k1_xboole_0))
% 1.29/1.54          | ((X60) = (k1_xboole_0))
% 1.29/1.54          | ((X59) = (k1_xboole_0)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.29/1.54  thf('46', plain,
% 1.29/1.54      ((((k1_xboole_0) != (k1_xboole_0))
% 1.29/1.54        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2)
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['44', '45'])).
% 1.29/1.54  thf('47', plain,
% 1.29/1.54      ((((sk_C) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2))),
% 1.29/1.54      inference('simplify', [status(thm)], ['46'])).
% 1.29/1.54  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('49', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('51', plain,
% 1.29/1.54      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2)),
% 1.29/1.54      inference('simplify_reflect-', [status(thm)], ['47', '48', '49', '50'])).
% 1.29/1.54  thf('52', plain,
% 1.29/1.54      (![X38 : $i, X39 : $i]:
% 1.29/1.54         (~ (r2_hidden @ X38 @ X39)
% 1.29/1.54          | (m1_subset_1 @ X38 @ X39)
% 1.29/1.54          | (v1_xboole_0 @ X39))),
% 1.29/1.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.29/1.54  thf('53', plain,
% 1.29/1.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.29/1.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.29/1.54  thf('54', plain,
% 1.29/1.54      (![X38 : $i, X39 : $i]:
% 1.29/1.54         ((m1_subset_1 @ X38 @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 1.29/1.54      inference('clc', [status(thm)], ['52', '53'])).
% 1.29/1.54  thf('55', plain,
% 1.29/1.54      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_2)),
% 1.29/1.54      inference('sup-', [status(thm)], ['51', '54'])).
% 1.29/1.54  thf('56', plain,
% 1.29/1.54      (![X67 : $i, X68 : $i, X69 : $i]:
% 1.29/1.54         (~ (m1_subset_1 @ X67 @ sk_B_2)
% 1.29/1.54          | ((sk_E_2) != (k3_mcart_1 @ X68 @ X67 @ X69))
% 1.29/1.54          | ((sk_D_2) = (X69))
% 1.29/1.54          | ~ (m1_subset_1 @ X69 @ sk_C)
% 1.29/1.54          | ~ (m1_subset_1 @ X68 @ sk_A))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('57', plain,
% 1.29/1.54      (![X0 : $i, X1 : $i]:
% 1.29/1.54         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.29/1.54          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.29/1.54          | ((sk_D_2) = (X1))
% 1.29/1.54          | ((sk_E_2)
% 1.29/1.54              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X1)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['55', '56'])).
% 1.29/1.54  thf('58', plain,
% 1.29/1.54      (![X0 : $i]:
% 1.29/1.54         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 1.29/1.54          | ((sk_D_2) = (X0))
% 1.29/1.54          | ~ (m1_subset_1 @ X0 @ sk_C)
% 1.29/1.54          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 1.29/1.54      inference('sup-', [status(thm)], ['39', '57'])).
% 1.29/1.54  thf('59', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['20', '23'])).
% 1.29/1.54  thf('60', plain,
% 1.29/1.54      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.29/1.54         ((r2_hidden @ (k1_mcart_1 @ X49) @ X50)
% 1.29/1.54          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ X50 @ X51)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.29/1.54  thf('61', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 1.29/1.54      inference('sup-', [status(thm)], ['59', '60'])).
% 1.29/1.54  thf('62', plain,
% 1.29/1.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.29/1.54      inference('sup-', [status(thm)], ['9', '10'])).
% 1.29/1.54  thf('63', plain,
% 1.29/1.54      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)
% 1.29/1.54        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['61', '62'])).
% 1.29/1.54  thf('64', plain,
% 1.29/1.54      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.29/1.54         (((k3_zfmisc_1 @ X59 @ X60 @ X61) != (k1_xboole_0))
% 1.29/1.54          | ((X61) = (k1_xboole_0))
% 1.29/1.54          | ((X60) = (k1_xboole_0))
% 1.29/1.54          | ((X59) = (k1_xboole_0)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.29/1.54  thf('65', plain,
% 1.29/1.54      ((((k1_xboole_0) != (k1_xboole_0))
% 1.29/1.54        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['63', '64'])).
% 1.29/1.54  thf('66', plain,
% 1.29/1.54      ((((sk_C) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 1.29/1.54      inference('simplify', [status(thm)], ['65'])).
% 1.29/1.54  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('68', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('70', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)),
% 1.29/1.54      inference('simplify_reflect-', [status(thm)], ['66', '67', '68', '69'])).
% 1.29/1.54  thf('71', plain,
% 1.29/1.54      (![X38 : $i, X39 : $i]:
% 1.29/1.54         ((m1_subset_1 @ X38 @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 1.29/1.54      inference('clc', [status(thm)], ['52', '53'])).
% 1.29/1.54  thf('72', plain,
% 1.29/1.54      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)),
% 1.29/1.54      inference('sup-', [status(thm)], ['70', '71'])).
% 1.29/1.54  thf('73', plain,
% 1.29/1.54      (![X0 : $i]:
% 1.29/1.54         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 1.29/1.54          | ((sk_D_2) = (X0))
% 1.29/1.54          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 1.29/1.54      inference('demod', [status(thm)], ['58', '72'])).
% 1.29/1.54  thf('74', plain,
% 1.29/1.54      ((((sk_E_2) != (sk_E_2))
% 1.29/1.54        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C)
% 1.29/1.54        | ((sk_D_2) = (k2_mcart_1 @ sk_E_2)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['19', '73'])).
% 1.29/1.54  thf('75', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['0', '1'])).
% 1.29/1.54  thf('76', plain,
% 1.29/1.54      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.29/1.54         ((k3_zfmisc_1 @ X46 @ X47 @ X48)
% 1.29/1.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47) @ X48))),
% 1.29/1.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.29/1.54  thf('77', plain,
% 1.29/1.54      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.29/1.54         ((r2_hidden @ (k2_mcart_1 @ X49) @ X51)
% 1.29/1.54          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ X50 @ X51)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.29/1.54  thf('78', plain,
% 1.29/1.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.29/1.54         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.29/1.54          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 1.29/1.54      inference('sup-', [status(thm)], ['76', '77'])).
% 1.29/1.54  thf('79', plain,
% 1.29/1.54      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.29/1.54        | (r2_hidden @ (k2_mcart_1 @ sk_E_2) @ sk_C))),
% 1.29/1.54      inference('sup-', [status(thm)], ['75', '78'])).
% 1.29/1.54  thf('80', plain,
% 1.29/1.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.29/1.54      inference('sup-', [status(thm)], ['9', '10'])).
% 1.29/1.54  thf('81', plain,
% 1.29/1.54      (((r2_hidden @ (k2_mcart_1 @ sk_E_2) @ sk_C)
% 1.29/1.54        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['79', '80'])).
% 1.29/1.54  thf('82', plain,
% 1.29/1.54      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.29/1.54         (((k3_zfmisc_1 @ X59 @ X60 @ X61) != (k1_xboole_0))
% 1.29/1.54          | ((X61) = (k1_xboole_0))
% 1.29/1.54          | ((X60) = (k1_xboole_0))
% 1.29/1.54          | ((X59) = (k1_xboole_0)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.29/1.54  thf('83', plain,
% 1.29/1.54      ((((k1_xboole_0) != (k1_xboole_0))
% 1.29/1.54        | (r2_hidden @ (k2_mcart_1 @ sk_E_2) @ sk_C)
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_C) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['81', '82'])).
% 1.29/1.54  thf('84', plain,
% 1.29/1.54      ((((sk_C) = (k1_xboole_0))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_A) = (k1_xboole_0))
% 1.29/1.54        | (r2_hidden @ (k2_mcart_1 @ sk_E_2) @ sk_C))),
% 1.29/1.54      inference('simplify', [status(thm)], ['83'])).
% 1.29/1.54  thf('85', plain, (((sk_A) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('86', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('87', plain, (((sk_C) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('88', plain, ((r2_hidden @ (k2_mcart_1 @ sk_E_2) @ sk_C)),
% 1.29/1.54      inference('simplify_reflect-', [status(thm)], ['84', '85', '86', '87'])).
% 1.29/1.54  thf('89', plain,
% 1.29/1.54      (![X38 : $i, X39 : $i]:
% 1.29/1.54         ((m1_subset_1 @ X38 @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 1.29/1.54      inference('clc', [status(thm)], ['52', '53'])).
% 1.29/1.54  thf('90', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C)),
% 1.29/1.54      inference('sup-', [status(thm)], ['88', '89'])).
% 1.29/1.54  thf('91', plain,
% 1.29/1.54      ((((sk_E_2) != (sk_E_2)) | ((sk_D_2) = (k2_mcart_1 @ sk_E_2)))),
% 1.29/1.54      inference('demod', [status(thm)], ['74', '90'])).
% 1.29/1.54  thf('92', plain, (((sk_D_2) = (k2_mcart_1 @ sk_E_2))),
% 1.29/1.54      inference('simplify', [status(thm)], ['91'])).
% 1.29/1.54  thf('93', plain,
% 1.29/1.54      (((sk_D_2) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('94', plain,
% 1.29/1.54      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf(t50_mcart_1, axiom,
% 1.29/1.54    (![A:$i,B:$i,C:$i]:
% 1.29/1.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.29/1.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.29/1.54          ( ~( ![D:$i]:
% 1.29/1.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.29/1.54                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.29/1.54                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.29/1.54                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.29/1.54                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.29/1.54                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.29/1.54  thf('95', plain,
% 1.29/1.54      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 1.29/1.54         (((X63) = (k1_xboole_0))
% 1.29/1.54          | ((X64) = (k1_xboole_0))
% 1.29/1.54          | ((k7_mcart_1 @ X63 @ X64 @ X66 @ X65) = (k2_mcart_1 @ X65))
% 1.29/1.54          | ~ (m1_subset_1 @ X65 @ (k3_zfmisc_1 @ X63 @ X64 @ X66))
% 1.29/1.54          | ((X66) = (k1_xboole_0)))),
% 1.29/1.54      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.29/1.54  thf('96', plain,
% 1.29/1.54      ((((sk_C) = (k1_xboole_0))
% 1.29/1.54        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))
% 1.29/1.54        | ((sk_B_2) = (k1_xboole_0))
% 1.29/1.54        | ((sk_A) = (k1_xboole_0)))),
% 1.29/1.54      inference('sup-', [status(thm)], ['94', '95'])).
% 1.29/1.54  thf('97', plain, (((sk_A) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('98', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('99', plain, (((sk_C) != (k1_xboole_0))),
% 1.29/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.54  thf('100', plain,
% 1.29/1.54      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 1.29/1.54      inference('simplify_reflect-', [status(thm)], ['96', '97', '98', '99'])).
% 1.29/1.54  thf('101', plain, (((sk_D_2) != (k2_mcart_1 @ sk_E_2))),
% 1.29/1.54      inference('demod', [status(thm)], ['93', '100'])).
% 1.29/1.54  thf('102', plain, ($false),
% 1.29/1.54      inference('simplify_reflect-', [status(thm)], ['92', '101'])).
% 1.29/1.54  
% 1.29/1.54  % SZS output end Refutation
% 1.29/1.54  
% 1.29/1.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
