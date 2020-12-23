%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GEgyC0A1tZ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:56 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 193 expanded)
%              Number of leaves         :   33 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          : 1095 (3721 expanded)
%              Number of equality atoms :  146 ( 539 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k3_zfmisc_1 @ X31 @ X32 @ X33 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t24_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50
        = ( k4_tarski @ ( k1_mcart_1 @ X50 ) @ ( k2_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k2_zfmisc_1 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X3
        = ( k4_tarski @ ( k1_mcart_1 @ X3 ) @ ( k2_mcart_1 @ X3 ) ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X21 @ X20 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_E_2
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k3_zfmisc_1 @ X31 @ X32 @ X33 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('17',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X46 ) @ X47 )
      | ~ ( r2_hidden @ X46 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( m1_subset_1 @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50
        = ( k4_tarski @ ( k1_mcart_1 @ X50 ) @ ( k2_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k2_zfmisc_1 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('29',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k3_zfmisc_1 @ X52 @ X53 @ X54 )
       != k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_mcart_1 @ sk_E_2 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_mcart_1 @ X28 @ X29 @ X30 )
      = ( k4_tarski @ ( k4_tarski @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('43',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X38 @ X39 @ X40 @ X41 ) @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k3_zfmisc_1 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('44',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X60 @ sk_B_2 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X61 @ X60 @ X62 ) )
      | ( sk_D_1 = X62 )
      | ~ ( m1_subset_1 @ X62 @ sk_C )
      | ~ ( m1_subset_1 @ X61 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_1 = X1 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X56 = k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X56 @ X57 @ X59 @ X58 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X58 @ ( k3_zfmisc_1 @ X56 @ X57 @ X59 ) )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_1 = X1 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('57',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X34 @ X35 @ X36 @ X37 ) @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k3_zfmisc_1 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('58',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X56 = k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X56 @ X57 @ X59 @ X58 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X58 @ ( k3_zfmisc_1 @ X56 @ X57 @ X59 ) )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('61',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','66'])).

thf('68',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['12','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('70',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X42 @ X43 @ X44 @ X45 ) @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k3_zfmisc_1 @ X42 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('71',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X56 = k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X56 @ X57 @ X59 @ X58 )
        = ( k2_mcart_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k3_zfmisc_1 @ X56 @ X57 @ X59 ) )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('74',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k2_mcart_1 @ sk_E_2 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,
    ( sk_D_1
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf('84',plain,(
    sk_D_1
 != ( k2_mcart_1 @ sk_E_2 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GEgyC0A1tZ
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.44/3.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.44/3.66  % Solved by: fo/fo7.sh
% 3.44/3.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.44/3.66  % done 4333 iterations in 3.194s
% 3.44/3.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.44/3.66  % SZS output start Refutation
% 3.44/3.66  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 3.44/3.66  thf(sk_A_type, type, sk_A: $i).
% 3.44/3.66  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 3.44/3.66  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 3.44/3.66  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 3.44/3.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.44/3.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.44/3.66  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 3.44/3.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.44/3.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.44/3.66  thf(sk_D_1_type, type, sk_D_1: $i).
% 3.44/3.66  thf(sk_C_type, type, sk_C: $i).
% 3.44/3.66  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.44/3.66  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 3.44/3.66  thf(sk_E_2_type, type, sk_E_2: $i).
% 3.44/3.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.44/3.66  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 3.44/3.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.44/3.66  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 3.44/3.66  thf(t71_mcart_1, conjecture,
% 3.44/3.66    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.44/3.66     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 3.44/3.66       ( ( ![F:$i]:
% 3.44/3.66           ( ( m1_subset_1 @ F @ A ) =>
% 3.44/3.66             ( ![G:$i]:
% 3.44/3.66               ( ( m1_subset_1 @ G @ B ) =>
% 3.44/3.66                 ( ![H:$i]:
% 3.44/3.66                   ( ( m1_subset_1 @ H @ C ) =>
% 3.44/3.66                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 3.44/3.66                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 3.44/3.66         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.44/3.66           ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.44/3.66           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 3.44/3.66  thf(zf_stmt_0, negated_conjecture,
% 3.44/3.66    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.44/3.66        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 3.44/3.66          ( ( ![F:$i]:
% 3.44/3.66              ( ( m1_subset_1 @ F @ A ) =>
% 3.44/3.66                ( ![G:$i]:
% 3.44/3.66                  ( ( m1_subset_1 @ G @ B ) =>
% 3.44/3.66                    ( ![H:$i]:
% 3.44/3.66                      ( ( m1_subset_1 @ H @ C ) =>
% 3.44/3.66                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 3.44/3.66                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 3.44/3.66            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.44/3.66              ( ( C ) = ( k1_xboole_0 ) ) | 
% 3.44/3.66              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 3.44/3.66    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 3.44/3.66  thf('0', plain,
% 3.44/3.66      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf(d3_zfmisc_1, axiom,
% 3.44/3.66    (![A:$i,B:$i,C:$i]:
% 3.44/3.66     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 3.44/3.66       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 3.44/3.66  thf('1', plain,
% 3.44/3.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.44/3.66         ((k3_zfmisc_1 @ X31 @ X32 @ X33)
% 3.44/3.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32) @ X33))),
% 3.44/3.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.44/3.66  thf(t24_mcart_1, axiom,
% 3.44/3.66    (![A:$i,B:$i]:
% 3.44/3.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.44/3.66          ( ~( ![C:$i]:
% 3.44/3.66               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 3.44/3.66                 ( ( C ) =
% 3.44/3.66                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 3.44/3.66  thf('2', plain,
% 3.44/3.66      (![X49 : $i, X50 : $i, X51 : $i]:
% 3.44/3.66         (((X49) = (k1_xboole_0))
% 3.44/3.66          | ((X50) = (k4_tarski @ (k1_mcart_1 @ X50) @ (k2_mcart_1 @ X50)))
% 3.44/3.66          | ~ (m1_subset_1 @ X50 @ (k2_zfmisc_1 @ X49 @ X51))
% 3.44/3.66          | ((X51) = (k1_xboole_0)))),
% 3.44/3.66      inference('cnf', [status(esa)], [t24_mcart_1])).
% 3.44/3.66  thf('3', plain,
% 3.44/3.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.44/3.66         (~ (m1_subset_1 @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 3.44/3.66          | ((X0) = (k1_xboole_0))
% 3.44/3.66          | ((X3) = (k4_tarski @ (k1_mcart_1 @ X3) @ (k2_mcart_1 @ X3)))
% 3.44/3.66          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['1', '2'])).
% 3.44/3.66  thf('4', plain,
% 3.44/3.66      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((sk_E_2)
% 3.44/3.66            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))
% 3.44/3.66        | ((sk_C) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['0', '3'])).
% 3.44/3.66  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('6', plain,
% 3.44/3.66      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((sk_E_2)
% 3.44/3.66            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 3.44/3.66  thf(t113_zfmisc_1, axiom,
% 3.44/3.66    (![A:$i,B:$i]:
% 3.44/3.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.44/3.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.44/3.66  thf('7', plain,
% 3.44/3.66      (![X20 : $i, X21 : $i]:
% 3.44/3.66         (((X20) = (k1_xboole_0))
% 3.44/3.66          | ((X21) = (k1_xboole_0))
% 3.44/3.66          | ((k2_zfmisc_1 @ X21 @ X20) != (k1_xboole_0)))),
% 3.44/3.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.44/3.66  thf('8', plain,
% 3.44/3.66      ((((k1_xboole_0) != (k1_xboole_0))
% 3.44/3.66        | ((sk_E_2)
% 3.44/3.66            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))
% 3.44/3.66        | ((sk_A) = (k1_xboole_0))
% 3.44/3.66        | ((sk_B_2) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['6', '7'])).
% 3.44/3.66  thf('9', plain,
% 3.44/3.66      ((((sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((sk_A) = (k1_xboole_0))
% 3.44/3.66        | ((sk_E_2)
% 3.44/3.66            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 3.44/3.66      inference('simplify', [status(thm)], ['8'])).
% 3.44/3.66  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('11', plain, (((sk_B_2) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('12', plain,
% 3.44/3.66      (((sk_E_2) = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['9', '10', '11'])).
% 3.44/3.66  thf('13', plain,
% 3.44/3.66      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf(d2_subset_1, axiom,
% 3.44/3.66    (![A:$i,B:$i]:
% 3.44/3.66     ( ( ( v1_xboole_0 @ A ) =>
% 3.44/3.66         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.44/3.66       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.44/3.66         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.44/3.66  thf('14', plain,
% 3.44/3.66      (![X23 : $i, X24 : $i]:
% 3.44/3.66         (~ (m1_subset_1 @ X23 @ X24)
% 3.44/3.66          | (r2_hidden @ X23 @ X24)
% 3.44/3.66          | (v1_xboole_0 @ X24))),
% 3.44/3.66      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.44/3.66  thf('15', plain,
% 3.44/3.66      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 3.44/3.66        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['13', '14'])).
% 3.44/3.66  thf('16', plain,
% 3.44/3.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.44/3.66         ((k3_zfmisc_1 @ X31 @ X32 @ X33)
% 3.44/3.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32) @ X33))),
% 3.44/3.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.44/3.66  thf(t10_mcart_1, axiom,
% 3.44/3.66    (![A:$i,B:$i,C:$i]:
% 3.44/3.66     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 3.44/3.66       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 3.44/3.66         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 3.44/3.66  thf('17', plain,
% 3.44/3.66      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.44/3.66         ((r2_hidden @ (k1_mcart_1 @ X46) @ X47)
% 3.44/3.66          | ~ (r2_hidden @ X46 @ (k2_zfmisc_1 @ X47 @ X48)))),
% 3.44/3.66      inference('cnf', [status(esa)], [t10_mcart_1])).
% 3.44/3.66  thf('18', plain,
% 3.44/3.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.44/3.66         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 3.44/3.66          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['16', '17'])).
% 3.44/3.66  thf('19', plain,
% 3.44/3.66      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 3.44/3.66        | (r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['15', '18'])).
% 3.44/3.66  thf(t7_xboole_0, axiom,
% 3.44/3.66    (![A:$i]:
% 3.44/3.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.44/3.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 3.44/3.66  thf('20', plain,
% 3.44/3.66      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 3.44/3.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.44/3.66  thf(d1_xboole_0, axiom,
% 3.44/3.66    (![A:$i]:
% 3.44/3.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.44/3.66  thf('21', plain,
% 3.44/3.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.44/3.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.44/3.66  thf('22', plain,
% 3.44/3.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.44/3.66      inference('sup-', [status(thm)], ['20', '21'])).
% 3.44/3.66  thf('23', plain,
% 3.44/3.66      (((r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 3.44/3.66        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['19', '22'])).
% 3.44/3.66  thf('24', plain,
% 3.44/3.66      (![X23 : $i, X24 : $i]:
% 3.44/3.66         (~ (r2_hidden @ X23 @ X24)
% 3.44/3.66          | (m1_subset_1 @ X23 @ X24)
% 3.44/3.66          | (v1_xboole_0 @ X24))),
% 3.44/3.66      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.44/3.66  thf('25', plain,
% 3.44/3.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.44/3.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.44/3.66  thf('26', plain,
% 3.44/3.66      (![X23 : $i, X24 : $i]:
% 3.44/3.66         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 3.44/3.66      inference('clc', [status(thm)], ['24', '25'])).
% 3.44/3.66  thf('27', plain,
% 3.44/3.66      ((((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 3.44/3.66        | (m1_subset_1 @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['23', '26'])).
% 3.44/3.66  thf('28', plain,
% 3.44/3.66      (![X49 : $i, X50 : $i, X51 : $i]:
% 3.44/3.66         (((X49) = (k1_xboole_0))
% 3.44/3.66          | ((X50) = (k4_tarski @ (k1_mcart_1 @ X50) @ (k2_mcart_1 @ X50)))
% 3.44/3.66          | ~ (m1_subset_1 @ X50 @ (k2_zfmisc_1 @ X49 @ X51))
% 3.44/3.66          | ((X51) = (k1_xboole_0)))),
% 3.44/3.66      inference('cnf', [status(esa)], [t24_mcart_1])).
% 3.44/3.66  thf('29', plain,
% 3.44/3.66      ((((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 3.44/3.66        | ((sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((k1_mcart_1 @ sk_E_2)
% 3.44/3.66            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 3.44/3.66               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))
% 3.44/3.66        | ((sk_A) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['27', '28'])).
% 3.44/3.66  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('31', plain, (((sk_B_2) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('32', plain,
% 3.44/3.66      ((((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 3.44/3.66        | ((k1_mcart_1 @ sk_E_2)
% 3.44/3.66            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 3.44/3.66               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['29', '30', '31'])).
% 3.44/3.66  thf(t35_mcart_1, axiom,
% 3.44/3.66    (![A:$i,B:$i,C:$i]:
% 3.44/3.66     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.44/3.66         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 3.44/3.66       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 3.44/3.66  thf('33', plain,
% 3.44/3.66      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.44/3.66         (((k3_zfmisc_1 @ X52 @ X53 @ X54) != (k1_xboole_0))
% 3.44/3.66          | ((X54) = (k1_xboole_0))
% 3.44/3.66          | ((X53) = (k1_xboole_0))
% 3.44/3.66          | ((X52) = (k1_xboole_0)))),
% 3.44/3.66      inference('cnf', [status(esa)], [t35_mcart_1])).
% 3.44/3.66  thf('34', plain,
% 3.44/3.66      ((((k1_xboole_0) != (k1_xboole_0))
% 3.44/3.66        | ((k1_mcart_1 @ sk_E_2)
% 3.44/3.66            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 3.44/3.66               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))
% 3.44/3.66        | ((sk_A) = (k1_xboole_0))
% 3.44/3.66        | ((sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((sk_C) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['32', '33'])).
% 3.44/3.66  thf('35', plain,
% 3.44/3.66      ((((sk_C) = (k1_xboole_0))
% 3.44/3.66        | ((sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((sk_A) = (k1_xboole_0))
% 3.44/3.66        | ((k1_mcart_1 @ sk_E_2)
% 3.44/3.66            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 3.44/3.66               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 3.44/3.66      inference('simplify', [status(thm)], ['34'])).
% 3.44/3.66  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('37', plain, (((sk_B_2) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('38', plain, (((sk_C) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('39', plain,
% 3.44/3.66      (((k1_mcart_1 @ sk_E_2)
% 3.44/3.66         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 3.44/3.66            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['35', '36', '37', '38'])).
% 3.44/3.66  thf(d3_mcart_1, axiom,
% 3.44/3.66    (![A:$i,B:$i,C:$i]:
% 3.44/3.66     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 3.44/3.66  thf('40', plain,
% 3.44/3.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.44/3.66         ((k3_mcart_1 @ X28 @ X29 @ X30)
% 3.44/3.66           = (k4_tarski @ (k4_tarski @ X28 @ X29) @ X30))),
% 3.44/3.66      inference('cnf', [status(esa)], [d3_mcart_1])).
% 3.44/3.66  thf('41', plain,
% 3.44/3.66      (![X0 : $i]:
% 3.44/3.66         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 3.44/3.66           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X0)
% 3.44/3.66           = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))),
% 3.44/3.66      inference('sup+', [status(thm)], ['39', '40'])).
% 3.44/3.66  thf('42', plain,
% 3.44/3.66      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf(dt_k6_mcart_1, axiom,
% 3.44/3.66    (![A:$i,B:$i,C:$i,D:$i]:
% 3.44/3.66     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 3.44/3.66       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 3.44/3.66  thf('43', plain,
% 3.44/3.66      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.44/3.66         ((m1_subset_1 @ (k6_mcart_1 @ X38 @ X39 @ X40 @ X41) @ X39)
% 3.44/3.66          | ~ (m1_subset_1 @ X41 @ (k3_zfmisc_1 @ X38 @ X39 @ X40)))),
% 3.44/3.66      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 3.44/3.66  thf('44', plain,
% 3.44/3.66      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ sk_B_2)),
% 3.44/3.66      inference('sup-', [status(thm)], ['42', '43'])).
% 3.44/3.66  thf('45', plain,
% 3.44/3.66      (![X60 : $i, X61 : $i, X62 : $i]:
% 3.44/3.66         (~ (m1_subset_1 @ X60 @ sk_B_2)
% 3.44/3.66          | ((sk_E_2) != (k3_mcart_1 @ X61 @ X60 @ X62))
% 3.44/3.66          | ((sk_D_1) = (X62))
% 3.44/3.66          | ~ (m1_subset_1 @ X62 @ sk_C)
% 3.44/3.66          | ~ (m1_subset_1 @ X61 @ sk_A))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('46', plain,
% 3.44/3.66      (![X0 : $i, X1 : $i]:
% 3.44/3.66         (~ (m1_subset_1 @ X0 @ sk_A)
% 3.44/3.66          | ~ (m1_subset_1 @ X1 @ sk_C)
% 3.44/3.66          | ((sk_D_1) = (X1))
% 3.44/3.66          | ((sk_E_2)
% 3.44/3.66              != (k3_mcart_1 @ X0 @ 
% 3.44/3.66                  (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ X1)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['44', '45'])).
% 3.44/3.66  thf('47', plain,
% 3.44/3.66      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf(t50_mcart_1, axiom,
% 3.44/3.66    (![A:$i,B:$i,C:$i]:
% 3.44/3.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.44/3.66          ( ( C ) != ( k1_xboole_0 ) ) & 
% 3.44/3.66          ( ~( ![D:$i]:
% 3.44/3.66               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 3.44/3.66                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 3.44/3.66                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 3.44/3.66                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 3.44/3.66                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 3.44/3.66                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 3.44/3.66  thf('48', plain,
% 3.44/3.66      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 3.44/3.66         (((X56) = (k1_xboole_0))
% 3.44/3.66          | ((X57) = (k1_xboole_0))
% 3.44/3.66          | ((k6_mcart_1 @ X56 @ X57 @ X59 @ X58)
% 3.44/3.66              = (k2_mcart_1 @ (k1_mcart_1 @ X58)))
% 3.44/3.66          | ~ (m1_subset_1 @ X58 @ (k3_zfmisc_1 @ X56 @ X57 @ X59))
% 3.44/3.66          | ((X59) = (k1_xboole_0)))),
% 3.44/3.66      inference('cnf', [status(esa)], [t50_mcart_1])).
% 3.44/3.66  thf('49', plain,
% 3.44/3.66      ((((sk_C) = (k1_xboole_0))
% 3.44/3.66        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 3.44/3.66            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))
% 3.44/3.66        | ((sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((sk_A) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['47', '48'])).
% 3.44/3.66  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('51', plain, (((sk_B_2) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('52', plain, (((sk_C) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('53', plain,
% 3.44/3.66      (((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 3.44/3.66         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['49', '50', '51', '52'])).
% 3.44/3.66  thf('54', plain,
% 3.44/3.66      (![X0 : $i, X1 : $i]:
% 3.44/3.66         (~ (m1_subset_1 @ X0 @ sk_A)
% 3.44/3.66          | ~ (m1_subset_1 @ X1 @ sk_C)
% 3.44/3.66          | ((sk_D_1) = (X1))
% 3.44/3.66          | ((sk_E_2)
% 3.44/3.66              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X1)))),
% 3.44/3.66      inference('demod', [status(thm)], ['46', '53'])).
% 3.44/3.66  thf('55', plain,
% 3.44/3.66      (![X0 : $i]:
% 3.44/3.66         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 3.44/3.66          | ((sk_D_1) = (X0))
% 3.44/3.66          | ~ (m1_subset_1 @ X0 @ sk_C)
% 3.44/3.66          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 3.44/3.66      inference('sup-', [status(thm)], ['41', '54'])).
% 3.44/3.66  thf('56', plain,
% 3.44/3.66      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf(dt_k5_mcart_1, axiom,
% 3.44/3.66    (![A:$i,B:$i,C:$i,D:$i]:
% 3.44/3.66     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 3.44/3.66       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 3.44/3.66  thf('57', plain,
% 3.44/3.66      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.44/3.66         ((m1_subset_1 @ (k5_mcart_1 @ X34 @ X35 @ X36 @ X37) @ X34)
% 3.44/3.66          | ~ (m1_subset_1 @ X37 @ (k3_zfmisc_1 @ X34 @ X35 @ X36)))),
% 3.44/3.66      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 3.44/3.66  thf('58', plain,
% 3.44/3.66      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ sk_A)),
% 3.44/3.66      inference('sup-', [status(thm)], ['56', '57'])).
% 3.44/3.66  thf('59', plain,
% 3.44/3.66      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('60', plain,
% 3.44/3.66      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 3.44/3.66         (((X56) = (k1_xboole_0))
% 3.44/3.66          | ((X57) = (k1_xboole_0))
% 3.44/3.66          | ((k5_mcart_1 @ X56 @ X57 @ X59 @ X58)
% 3.44/3.66              = (k1_mcart_1 @ (k1_mcart_1 @ X58)))
% 3.44/3.66          | ~ (m1_subset_1 @ X58 @ (k3_zfmisc_1 @ X56 @ X57 @ X59))
% 3.44/3.66          | ((X59) = (k1_xboole_0)))),
% 3.44/3.66      inference('cnf', [status(esa)], [t50_mcart_1])).
% 3.44/3.66  thf('61', plain,
% 3.44/3.66      ((((sk_C) = (k1_xboole_0))
% 3.44/3.66        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 3.44/3.66            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))
% 3.44/3.66        | ((sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((sk_A) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['59', '60'])).
% 3.44/3.66  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('63', plain, (((sk_B_2) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('64', plain, (((sk_C) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('65', plain,
% 3.44/3.66      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 3.44/3.66         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['61', '62', '63', '64'])).
% 3.44/3.66  thf('66', plain,
% 3.44/3.66      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)),
% 3.44/3.66      inference('demod', [status(thm)], ['58', '65'])).
% 3.44/3.66  thf('67', plain,
% 3.44/3.66      (![X0 : $i]:
% 3.44/3.66         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 3.44/3.66          | ((sk_D_1) = (X0))
% 3.44/3.66          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 3.44/3.66      inference('demod', [status(thm)], ['55', '66'])).
% 3.44/3.66  thf('68', plain,
% 3.44/3.66      ((((sk_E_2) != (sk_E_2))
% 3.44/3.66        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C)
% 3.44/3.66        | ((sk_D_1) = (k2_mcart_1 @ sk_E_2)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['12', '67'])).
% 3.44/3.66  thf('69', plain,
% 3.44/3.66      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf(dt_k7_mcart_1, axiom,
% 3.44/3.66    (![A:$i,B:$i,C:$i,D:$i]:
% 3.44/3.66     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 3.44/3.66       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 3.44/3.66  thf('70', plain,
% 3.44/3.66      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 3.44/3.66         ((m1_subset_1 @ (k7_mcart_1 @ X42 @ X43 @ X44 @ X45) @ X44)
% 3.44/3.66          | ~ (m1_subset_1 @ X45 @ (k3_zfmisc_1 @ X42 @ X43 @ X44)))),
% 3.44/3.66      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 3.44/3.66  thf('71', plain,
% 3.44/3.66      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ sk_C)),
% 3.44/3.66      inference('sup-', [status(thm)], ['69', '70'])).
% 3.44/3.66  thf('72', plain,
% 3.44/3.66      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('73', plain,
% 3.44/3.66      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 3.44/3.66         (((X56) = (k1_xboole_0))
% 3.44/3.66          | ((X57) = (k1_xboole_0))
% 3.44/3.66          | ((k7_mcart_1 @ X56 @ X57 @ X59 @ X58) = (k2_mcart_1 @ X58))
% 3.44/3.66          | ~ (m1_subset_1 @ X58 @ (k3_zfmisc_1 @ X56 @ X57 @ X59))
% 3.44/3.66          | ((X59) = (k1_xboole_0)))),
% 3.44/3.66      inference('cnf', [status(esa)], [t50_mcart_1])).
% 3.44/3.66  thf('74', plain,
% 3.44/3.66      ((((sk_C) = (k1_xboole_0))
% 3.44/3.66        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))
% 3.44/3.66        | ((sk_B_2) = (k1_xboole_0))
% 3.44/3.66        | ((sk_A) = (k1_xboole_0)))),
% 3.44/3.66      inference('sup-', [status(thm)], ['72', '73'])).
% 3.44/3.66  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('76', plain, (((sk_B_2) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('77', plain, (((sk_C) != (k1_xboole_0))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('78', plain,
% 3.44/3.66      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 3.44/3.66  thf('79', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C)),
% 3.44/3.66      inference('demod', [status(thm)], ['71', '78'])).
% 3.44/3.66  thf('80', plain,
% 3.44/3.66      ((((sk_E_2) != (sk_E_2)) | ((sk_D_1) = (k2_mcart_1 @ sk_E_2)))),
% 3.44/3.66      inference('demod', [status(thm)], ['68', '79'])).
% 3.44/3.66  thf('81', plain, (((sk_D_1) = (k2_mcart_1 @ sk_E_2))),
% 3.44/3.66      inference('simplify', [status(thm)], ['80'])).
% 3.44/3.66  thf('82', plain,
% 3.44/3.66      (((sk_D_1) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2))),
% 3.44/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.66  thf('83', plain,
% 3.44/3.66      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 3.44/3.66  thf('84', plain, (((sk_D_1) != (k2_mcart_1 @ sk_E_2))),
% 3.44/3.66      inference('demod', [status(thm)], ['82', '83'])).
% 3.44/3.66  thf('85', plain, ($false),
% 3.44/3.66      inference('simplify_reflect-', [status(thm)], ['81', '84'])).
% 3.44/3.66  
% 3.44/3.66  % SZS output end Refutation
% 3.44/3.66  
% 3.44/3.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
