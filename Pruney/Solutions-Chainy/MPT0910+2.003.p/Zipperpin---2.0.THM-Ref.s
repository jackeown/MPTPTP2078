%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c6Km6GWWF0

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:52 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 283 expanded)
%              Number of leaves         :   39 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          : 1331 (4317 expanded)
%              Number of equality atoms :  171 ( 609 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t70_mcart_1,conjecture,(
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
                     => ( D = G ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = G ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50
        = ( k4_tarski @ ( k1_mcart_1 @ X50 ) @ ( k2_mcart_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_zfmisc_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_zfmisc_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X18: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['19','21'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( ( k4_zfmisc_1 @ X56 @ X57 @ X58 @ X59 )
       != k1_xboole_0 )
      | ( X59 = k1_xboole_0 )
      | ( X58 = k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( X56 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k1_xboole_0 != sk_E )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('32',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('35',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50
        = ( k4_tarski @ ( k1_mcart_1 @ X50 ) @ ( k2_mcart_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X17 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_mcart_1 @ X25 @ X26 @ X27 )
      = ( k4_tarski @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('60',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X39 @ X40 @ X41 @ X42 ) @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k3_zfmisc_1 @ X39 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('61',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ sk_B_1 )
      | ( sk_D_1 = X61 )
      | ( sk_E
       != ( k3_mcart_1 @ X62 @ X61 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X62 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) @ X1 ) )
      | ( sk_D_1
        = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_D_1
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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

thf('67',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X52 @ X53 @ X55 @ X54 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X54 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k3_zfmisc_1 @ X52 @ X53 @ X55 ) )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('68',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('76',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X35 @ X36 @ X37 @ X38 ) @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k3_zfmisc_1 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('77',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X52 @ X53 @ X55 @ X54 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X54 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k3_zfmisc_1 @ X52 @ X53 @ X55 ) )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('80',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['77','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['74','85'])).

thf('87',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('89',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('90',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X52 @ X53 @ X55 @ X54 )
        = ( k2_mcart_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k3_zfmisc_1 @ X52 @ X53 @ X55 ) )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('93',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['90','97'])).

thf('99',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','98'])).

thf('100',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X17 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c6Km6GWWF0
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.95  % Solved by: fo/fo7.sh
% 0.74/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.95  % done 633 iterations in 0.500s
% 0.74/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.95  % SZS output start Refutation
% 0.74/0.95  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.74/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.95  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.74/0.95  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.74/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.95  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.74/0.95  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.74/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.95  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.74/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.95  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.74/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.95  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.74/0.95  thf(sk_B_type, type, sk_B: $i > $i).
% 0.74/0.95  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.74/0.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.74/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.95  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.74/0.95  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.74/0.95  thf(sk_E_type, type, sk_E: $i).
% 0.74/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.74/0.95  thf(t70_mcart_1, conjecture,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.74/0.95       ( ( ![F:$i]:
% 0.74/0.95           ( ( m1_subset_1 @ F @ A ) =>
% 0.74/0.95             ( ![G:$i]:
% 0.74/0.95               ( ( m1_subset_1 @ G @ B ) =>
% 0.74/0.95                 ( ![H:$i]:
% 0.74/0.95                   ( ( m1_subset_1 @ H @ C ) =>
% 0.74/0.95                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.74/0.95                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.74/0.95         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.74/0.95           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.74/0.95           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.74/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.95    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.74/0.95        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.74/0.95          ( ( ![F:$i]:
% 0.74/0.95              ( ( m1_subset_1 @ F @ A ) =>
% 0.74/0.95                ( ![G:$i]:
% 0.74/0.95                  ( ( m1_subset_1 @ G @ B ) =>
% 0.74/0.95                    ( ![H:$i]:
% 0.74/0.95                      ( ( m1_subset_1 @ H @ C ) =>
% 0.74/0.95                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.74/0.95                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.74/0.95            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.74/0.95              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.74/0.95              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.74/0.95    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.74/0.95  thf('0', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(t2_subset, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ A @ B ) =>
% 0.74/0.95       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.74/0.95  thf('1', plain,
% 0.74/0.95      (![X21 : $i, X22 : $i]:
% 0.74/0.95         ((r2_hidden @ X21 @ X22)
% 0.74/0.95          | (v1_xboole_0 @ X22)
% 0.74/0.95          | ~ (m1_subset_1 @ X21 @ X22))),
% 0.74/0.95      inference('cnf', [status(esa)], [t2_subset])).
% 0.74/0.95  thf('2', plain,
% 0.74/0.95      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.74/0.95        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['0', '1'])).
% 0.74/0.95  thf(t23_mcart_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( v1_relat_1 @ B ) =>
% 0.74/0.95       ( ( r2_hidden @ A @ B ) =>
% 0.74/0.95         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.74/0.95  thf('3', plain,
% 0.74/0.95      (![X50 : $i, X51 : $i]:
% 0.74/0.95         (((X50) = (k4_tarski @ (k1_mcart_1 @ X50) @ (k2_mcart_1 @ X50)))
% 0.74/0.95          | ~ (v1_relat_1 @ X51)
% 0.74/0.95          | ~ (r2_hidden @ X50 @ X51))),
% 0.74/0.95      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.74/0.95  thf('4', plain,
% 0.74/0.95      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.74/0.95        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.74/0.95        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.74/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/0.95  thf(d3_zfmisc_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.74/0.95       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.74/0.95  thf('5', plain,
% 0.74/0.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.74/0.95         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 0.74/0.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 0.74/0.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.74/0.95  thf(fc6_relat_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.74/0.95  thf('6', plain,
% 0.74/0.95      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.74/0.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/0.95  thf('7', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.74/0.95      inference('sup+', [status(thm)], ['5', '6'])).
% 0.74/0.95  thf('8', plain,
% 0.74/0.95      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.74/0.95        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.74/0.95      inference('demod', [status(thm)], ['4', '7'])).
% 0.74/0.95  thf(t2_tarski, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.74/0.95       ( ( A ) = ( B ) ) ))).
% 0.74/0.95  thf('9', plain,
% 0.74/0.95      (![X3 : $i, X4 : $i]:
% 0.74/0.95         (((X4) = (X3))
% 0.74/0.95          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.74/0.95          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.74/0.95      inference('cnf', [status(esa)], [t2_tarski])).
% 0.74/0.95  thf(t113_zfmisc_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.74/0.95       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.74/0.95  thf('10', plain,
% 0.74/0.95      (![X17 : $i, X18 : $i]:
% 0.74/0.95         (((k2_zfmisc_1 @ X17 @ X18) = (k1_xboole_0))
% 0.74/0.95          | ((X18) != (k1_xboole_0)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.74/0.95  thf('11', plain,
% 0.74/0.95      (![X17 : $i]: ((k2_zfmisc_1 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['10'])).
% 0.74/0.95  thf(t152_zfmisc_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.74/0.95  thf('12', plain,
% 0.74/0.95      (![X19 : $i, X20 : $i]: ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.74/0.95      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.74/0.95  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.74/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.74/0.95  thf('14', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['9', '13'])).
% 0.74/0.95  thf(d1_xboole_0, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.74/0.95  thf('15', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.74/0.95      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.95  thf('16', plain,
% 0.74/0.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.95  thf('17', plain,
% 0.74/0.95      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.74/0.95        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['8', '16'])).
% 0.74/0.95  thf(d4_zfmisc_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.95     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.74/0.95       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.74/0.95  thf('18', plain,
% 0.74/0.95      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.74/0.95         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 0.74/0.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 0.74/0.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.74/0.95  thf('19', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 0.74/0.95            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.74/0.95          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.74/0.95      inference('sup+', [status(thm)], ['17', '18'])).
% 0.74/0.95  thf('20', plain,
% 0.74/0.95      (![X17 : $i, X18 : $i]:
% 0.74/0.95         (((k2_zfmisc_1 @ X17 @ X18) = (k1_xboole_0))
% 0.74/0.95          | ((X17) != (k1_xboole_0)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.74/0.95  thf('21', plain,
% 0.74/0.95      (![X18 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['20'])).
% 0.74/0.95  thf('22', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.74/0.95          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.74/0.95      inference('demod', [status(thm)], ['19', '21'])).
% 0.74/0.95  thf(t55_mcart_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.95     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.74/0.95         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.74/0.95       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.74/0.95  thf('23', plain,
% 0.74/0.95      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.74/0.95         (((k4_zfmisc_1 @ X56 @ X57 @ X58 @ X59) != (k1_xboole_0))
% 0.74/0.95          | ((X59) = (k1_xboole_0))
% 0.74/0.95          | ((X58) = (k1_xboole_0))
% 0.74/0.95          | ((X57) = (k1_xboole_0))
% 0.74/0.95          | ((X56) = (k1_xboole_0)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.74/0.95  thf('24', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((k1_xboole_0) != (k1_xboole_0))
% 0.74/0.95          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.74/0.95          | ((sk_A) = (k1_xboole_0))
% 0.74/0.95          | ((sk_B_1) = (k1_xboole_0))
% 0.74/0.95          | ((sk_C_1) = (k1_xboole_0))
% 0.74/0.95          | ((X0) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['22', '23'])).
% 0.74/0.95  thf('25', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((X0) = (k1_xboole_0))
% 0.74/0.95          | ((sk_C_1) = (k1_xboole_0))
% 0.74/0.95          | ((sk_B_1) = (k1_xboole_0))
% 0.74/0.95          | ((sk_A) = (k1_xboole_0))
% 0.74/0.95          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.74/0.95      inference('simplify', [status(thm)], ['24'])).
% 0.74/0.95  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('27', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('28', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('29', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((X0) = (k1_xboole_0))
% 0.74/0.95          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.74/0.95  thf('30', plain,
% 0.74/0.95      ((((k1_xboole_0) != (sk_E))
% 0.74/0.95        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.74/0.95      inference('eq_fact', [status(thm)], ['29'])).
% 0.74/0.95  thf('31', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((X0) = (k1_xboole_0))
% 0.74/0.95          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.74/0.95  thf('32', plain,
% 0.74/0.95      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.74/0.95      inference('clc', [status(thm)], ['30', '31'])).
% 0.74/0.95  thf('33', plain,
% 0.74/0.95      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.74/0.95        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['0', '1'])).
% 0.74/0.95  thf('34', plain,
% 0.74/0.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.74/0.95         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 0.74/0.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 0.74/0.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.74/0.95  thf(t10_mcart_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.74/0.95       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.74/0.95         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.74/0.95  thf('35', plain,
% 0.74/0.95      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.74/0.95         ((r2_hidden @ (k1_mcart_1 @ X47) @ X48)
% 0.74/0.95          | ~ (r2_hidden @ X47 @ (k2_zfmisc_1 @ X48 @ X49)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.74/0.95  thf('36', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.74/0.95          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['34', '35'])).
% 0.74/0.95  thf('37', plain,
% 0.74/0.95      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.74/0.95        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['33', '36'])).
% 0.74/0.95  thf('38', plain,
% 0.74/0.95      (![X50 : $i, X51 : $i]:
% 0.74/0.95         (((X50) = (k4_tarski @ (k1_mcart_1 @ X50) @ (k2_mcart_1 @ X50)))
% 0.74/0.95          | ~ (v1_relat_1 @ X51)
% 0.74/0.95          | ~ (r2_hidden @ X50 @ X51))),
% 0.74/0.95      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.74/0.95  thf('39', plain,
% 0.74/0.95      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.74/0.95        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.74/0.95        | ((k1_mcart_1 @ sk_E)
% 0.74/0.95            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.74/0.95               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.74/0.95      inference('sup-', [status(thm)], ['37', '38'])).
% 0.74/0.95  thf('40', plain,
% 0.74/0.95      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.74/0.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/0.95  thf('41', plain,
% 0.74/0.95      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.74/0.95        | ((k1_mcart_1 @ sk_E)
% 0.74/0.95            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.74/0.95               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.74/0.95      inference('demod', [status(thm)], ['39', '40'])).
% 0.74/0.95  thf('42', plain,
% 0.74/0.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.95  thf('43', plain,
% 0.74/0.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.95  thf('44', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.74/0.95      inference('sup+', [status(thm)], ['42', '43'])).
% 0.74/0.95  thf('45', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((k1_mcart_1 @ sk_E)
% 0.74/0.95            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.74/0.95               (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.74/0.95          | ~ (v1_xboole_0 @ X0)
% 0.74/0.95          | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (X0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['41', '44'])).
% 0.74/0.95  thf('46', plain,
% 0.74/0.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.74/0.95         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 0.74/0.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 0.74/0.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.74/0.95  thf('47', plain,
% 0.74/0.95      (![X16 : $i, X17 : $i]:
% 0.74/0.95         (((X16) = (k1_xboole_0))
% 0.74/0.95          | ((X17) = (k1_xboole_0))
% 0.74/0.95          | ((k2_zfmisc_1 @ X17 @ X16) != (k1_xboole_0)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.74/0.95  thf('48', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.74/0.95          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.74/0.95          | ((X0) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['46', '47'])).
% 0.74/0.95  thf('49', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((X0) != (k1_xboole_0))
% 0.74/0.95          | ~ (v1_xboole_0 @ X0)
% 0.74/0.95          | ((k1_mcart_1 @ sk_E)
% 0.74/0.95              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.74/0.95                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.74/0.95          | ((sk_C_1) = (k1_xboole_0))
% 0.74/0.95          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['45', '48'])).
% 0.74/0.95  thf('50', plain,
% 0.74/0.95      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.74/0.95        | ((sk_C_1) = (k1_xboole_0))
% 0.74/0.95        | ((k1_mcart_1 @ sk_E)
% 0.74/0.95            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.74/0.95               (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.74/0.95        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['49'])).
% 0.74/0.95  thf('51', plain,
% 0.74/0.95      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.74/0.95      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.95  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.74/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.74/0.95  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.95      inference('sup-', [status(thm)], ['51', '52'])).
% 0.74/0.95  thf('54', plain,
% 0.74/0.95      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.74/0.95        | ((sk_C_1) = (k1_xboole_0))
% 0.74/0.95        | ((k1_mcart_1 @ sk_E)
% 0.74/0.95            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.74/0.95               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.74/0.95      inference('simplify_reflect+', [status(thm)], ['50', '53'])).
% 0.74/0.95  thf('55', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('56', plain,
% 0.74/0.95      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.74/0.95        | ((k1_mcart_1 @ sk_E)
% 0.74/0.95            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.74/0.95               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.74/0.95  thf(d3_mcart_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.74/0.95  thf('57', plain,
% 0.74/0.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.74/0.95         ((k3_mcart_1 @ X25 @ X26 @ X27)
% 0.74/0.95           = (k4_tarski @ (k4_tarski @ X25 @ X26) @ X27))),
% 0.74/0.95      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.74/0.95  thf('58', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.74/0.95            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.74/0.95            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.74/0.95          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup+', [status(thm)], ['56', '57'])).
% 0.74/0.95  thf('59', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(dt_k6_mcart_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.74/0.95       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.74/0.95  thf('60', plain,
% 0.74/0.95      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.74/0.95         ((m1_subset_1 @ (k6_mcart_1 @ X39 @ X40 @ X41 @ X42) @ X40)
% 0.74/0.95          | ~ (m1_subset_1 @ X42 @ (k3_zfmisc_1 @ X39 @ X40 @ X41)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.74/0.95  thf('61', plain,
% 0.74/0.95      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E) @ sk_B_1)),
% 0.74/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.74/0.95  thf('62', plain,
% 0.74/0.95      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X61 @ sk_B_1)
% 0.74/0.95          | ((sk_D_1) = (X61))
% 0.74/0.95          | ((sk_E) != (k3_mcart_1 @ X62 @ X61 @ X63))
% 0.74/0.95          | ~ (m1_subset_1 @ X63 @ sk_C_1)
% 0.74/0.95          | ~ (m1_subset_1 @ X62 @ sk_A))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('63', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.74/0.95          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.74/0.95          | ((sk_E)
% 0.74/0.95              != (k3_mcart_1 @ X0 @ 
% 0.74/0.95                  (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E) @ X1))
% 0.74/0.95          | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['61', '62'])).
% 0.74/0.95  thf('64', plain,
% 0.74/0.95      (((sk_D_1) != (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('65', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.74/0.95          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.74/0.95          | ((sk_E)
% 0.74/0.95              != (k3_mcart_1 @ X0 @ 
% 0.74/0.95                  (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E) @ X1)))),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.74/0.95  thf('66', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(t50_mcart_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.74/0.95          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.74/0.95          ( ~( ![D:$i]:
% 0.74/0.95               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.74/0.95                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.74/0.95                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.74/0.95                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.74/0.95                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.74/0.95                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.74/0.95  thf('67', plain,
% 0.74/0.95      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.74/0.95         (((X52) = (k1_xboole_0))
% 0.74/0.95          | ((X53) = (k1_xboole_0))
% 0.74/0.95          | ((k6_mcart_1 @ X52 @ X53 @ X55 @ X54)
% 0.74/0.95              = (k2_mcart_1 @ (k1_mcart_1 @ X54)))
% 0.74/0.95          | ~ (m1_subset_1 @ X54 @ (k3_zfmisc_1 @ X52 @ X53 @ X55))
% 0.74/0.95          | ((X55) = (k1_xboole_0)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.74/0.95  thf('68', plain,
% 0.74/0.95      ((((sk_C_1) = (k1_xboole_0))
% 0.74/0.95        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)
% 0.74/0.95            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.74/0.95        | ((sk_B_1) = (k1_xboole_0))
% 0.74/0.95        | ((sk_A) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['66', '67'])).
% 0.74/0.95  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('70', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('71', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('72', plain,
% 0.74/0.95      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)
% 0.74/0.95         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['68', '69', '70', '71'])).
% 0.74/0.95  thf('73', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.74/0.95          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.74/0.95          | ((sk_E)
% 0.74/0.95              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.74/0.95      inference('demod', [status(thm)], ['65', '72'])).
% 0.74/0.95  thf('74', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.74/0.95          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.74/0.95          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 0.74/0.95          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.74/0.95      inference('sup-', [status(thm)], ['58', '73'])).
% 0.74/0.95  thf('75', plain,
% 0.74/0.95      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(dt_k5_mcart_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.74/0.95       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 0.74/0.95  thf('76', plain,
% 0.74/0.95      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.74/0.95         ((m1_subset_1 @ (k5_mcart_1 @ X35 @ X36 @ X37 @ X38) @ X35)
% 0.74/0.95          | ~ (m1_subset_1 @ X38 @ (k3_zfmisc_1 @ X35 @ X36 @ X37)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 0.74/0.95  thf('77', plain,
% 0.74/0.95      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.74/0.96      inference('sup-', [status(thm)], ['75', '76'])).
% 0.74/0.96  thf('78', plain,
% 0.74/0.96      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('79', plain,
% 0.74/0.96      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.74/0.96         (((X52) = (k1_xboole_0))
% 0.74/0.96          | ((X53) = (k1_xboole_0))
% 0.74/0.96          | ((k5_mcart_1 @ X52 @ X53 @ X55 @ X54)
% 0.74/0.96              = (k1_mcart_1 @ (k1_mcart_1 @ X54)))
% 0.74/0.96          | ~ (m1_subset_1 @ X54 @ (k3_zfmisc_1 @ X52 @ X53 @ X55))
% 0.74/0.96          | ((X55) = (k1_xboole_0)))),
% 0.74/0.96      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.74/0.96  thf('80', plain,
% 0.74/0.96      ((((sk_C_1) = (k1_xboole_0))
% 0.74/0.96        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)
% 0.74/0.96            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.74/0.96        | ((sk_B_1) = (k1_xboole_0))
% 0.74/0.96        | ((sk_A) = (k1_xboole_0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['78', '79'])).
% 0.74/0.96  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('82', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('83', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('84', plain,
% 0.74/0.96      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)
% 0.74/0.96         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.74/0.96      inference('simplify_reflect-', [status(thm)], ['80', '81', '82', '83'])).
% 0.74/0.96  thf('85', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.74/0.96      inference('demod', [status(thm)], ['77', '84'])).
% 0.74/0.96  thf('86', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.74/0.96          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.74/0.96          | ~ (m1_subset_1 @ X0 @ sk_C_1))),
% 0.74/0.96      inference('demod', [status(thm)], ['74', '85'])).
% 0.74/0.96  thf('87', plain,
% 0.74/0.96      ((((sk_E) != (sk_E))
% 0.74/0.96        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C_1)
% 0.74/0.96        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['32', '86'])).
% 0.74/0.96  thf('88', plain,
% 0.74/0.96      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf(dt_k7_mcart_1, axiom,
% 0.74/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.96     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.74/0.96       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.74/0.96  thf('89', plain,
% 0.74/0.96      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.74/0.96         ((m1_subset_1 @ (k7_mcart_1 @ X43 @ X44 @ X45 @ X46) @ X45)
% 0.74/0.96          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X43 @ X44 @ X45)))),
% 0.74/0.96      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.74/0.96  thf('90', plain,
% 0.74/0.96      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.74/0.96      inference('sup-', [status(thm)], ['88', '89'])).
% 0.74/0.96  thf('91', plain,
% 0.74/0.96      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('92', plain,
% 0.74/0.96      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.74/0.96         (((X52) = (k1_xboole_0))
% 0.74/0.96          | ((X53) = (k1_xboole_0))
% 0.74/0.96          | ((k7_mcart_1 @ X52 @ X53 @ X55 @ X54) = (k2_mcart_1 @ X54))
% 0.74/0.96          | ~ (m1_subset_1 @ X54 @ (k3_zfmisc_1 @ X52 @ X53 @ X55))
% 0.74/0.96          | ((X55) = (k1_xboole_0)))),
% 0.74/0.96      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.74/0.96  thf('93', plain,
% 0.74/0.96      ((((sk_C_1) = (k1_xboole_0))
% 0.74/0.96        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.74/0.96        | ((sk_B_1) = (k1_xboole_0))
% 0.74/0.96        | ((sk_A) = (k1_xboole_0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['91', '92'])).
% 0.74/0.96  thf('94', plain, (((sk_A) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('95', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('96', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('97', plain,
% 0.74/0.96      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.74/0.96      inference('simplify_reflect-', [status(thm)], ['93', '94', '95', '96'])).
% 0.74/0.96  thf('98', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C_1)),
% 0.74/0.96      inference('demod', [status(thm)], ['90', '97'])).
% 0.74/0.96  thf('99', plain,
% 0.74/0.96      ((((sk_E) != (sk_E)) | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('demod', [status(thm)], ['87', '98'])).
% 0.74/0.96  thf('100', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.74/0.96      inference('simplify', [status(thm)], ['99'])).
% 0.74/0.96  thf('101', plain,
% 0.74/0.96      (![X16 : $i, X17 : $i]:
% 0.74/0.96         (((X16) = (k1_xboole_0))
% 0.74/0.96          | ((X17) = (k1_xboole_0))
% 0.74/0.96          | ((k2_zfmisc_1 @ X17 @ X16) != (k1_xboole_0)))),
% 0.74/0.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.74/0.96  thf('102', plain,
% 0.74/0.96      ((((k1_xboole_0) != (k1_xboole_0))
% 0.74/0.96        | ((sk_A) = (k1_xboole_0))
% 0.74/0.96        | ((sk_B_1) = (k1_xboole_0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['100', '101'])).
% 0.74/0.96  thf('103', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.74/0.96      inference('simplify', [status(thm)], ['102'])).
% 0.74/0.96  thf('104', plain, (((sk_A) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('105', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('106', plain, ($false),
% 0.74/0.96      inference('simplify_reflect-', [status(thm)], ['103', '104', '105'])).
% 0.74/0.96  
% 0.74/0.96  % SZS output end Refutation
% 0.74/0.96  
% 0.74/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
