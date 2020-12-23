%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3rgkz5b2Q1

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:13 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 275 expanded)
%              Number of leaves         :   39 (  99 expanded)
%              Depth                    :   21
%              Number of atoms          : 1643 (6201 expanded)
%              Number of equality atoms :  178 ( 812 expanded)
%              Maximal formula depth    :   24 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t81_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( ! [G: $i] :
            ( ( m1_subset_1 @ G @ A )
           => ! [H: $i] :
                ( ( m1_subset_1 @ H @ B )
               => ! [I: $i] :
                    ( ( m1_subset_1 @ I @ C )
                   => ! [J: $i] :
                        ( ( m1_subset_1 @ J @ D )
                       => ( ( F
                            = ( k4_mcart_1 @ G @ H @ I @ J ) )
                         => ( E = I ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ( ! [G: $i] :
              ( ( m1_subset_1 @ G @ A )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ B )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ C )
                     => ! [J: $i] :
                          ( ( m1_subset_1 @ J @ D )
                         => ( ( F
                              = ( k4_mcart_1 @ G @ H @ I @ J ) )
                           => ( E = I ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( r2_hidden @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42
        = ( k4_tarski @ ( k1_mcart_1 @ X42 ) @ ( k2_mcart_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_F
      = ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ ( k2_mcart_1 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_F
      = ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ ( k2_mcart_1 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,
    ( ( sk_F
      = ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ ( k2_mcart_1 @ sk_F ) ) )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( ( k4_zfmisc_1 @ X44 @ X45 @ X46 @ X47 )
       != k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('12',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F
      = ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ ( k2_mcart_1 @ sk_F ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F
      = ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ ( k2_mcart_1 @ sk_F ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_F
    = ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ ( k2_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( r2_hidden @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X39 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_F ) @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42
        = ( k4_tarski @ ( k1_mcart_1 @ X42 ) @ ( k2_mcart_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_F )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( ( k1_mcart_1 @ sk_F )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ X0 ) )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_F ) @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X39 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42
        = ( k4_tarski @ ( k1_mcart_1 @ X42 ) @ ( k2_mcart_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ X1 @ X0 )
        = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('48',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X34 @ X35 @ X36 @ X37 @ X38 ) @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k4_zfmisc_1 @ X34 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('49',plain,(
    m1_subset_1 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf('51',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X52 ) ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('52',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X54 @ sk_B )
      | ~ ( m1_subset_1 @ X55 @ sk_D )
      | ( sk_F
       != ( k4_mcart_1 @ X56 @ X54 @ X57 @ X55 ) )
      | ( sk_E = X57 )
      | ~ ( m1_subset_1 @ X57 @ sk_C )
      | ~ ( m1_subset_1 @ X56 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E = X1 )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_F
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ sk_D )
      | ( sk_E = X1 )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X29 @ X30 @ X31 @ X32 @ X33 ) @ X29 )
      | ~ ( m1_subset_1 @ X33 @ ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('64',plain,(
    m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X52 ) ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('67',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_F
       != ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ sk_D )
      | ( sk_E = X1 )
      | ~ ( m1_subset_1 @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( sk_F
       != ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ X0 ) )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ sk_C )
      | ( sk_E
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_D )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['31','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ) )).

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X19 @ X20 @ X21 @ X22 @ X23 ) @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('78',plain,(
    m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_C ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('81',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ sk_C ),
    inference(demod,[status(thm)],['78','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( sk_F
       != ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ X0 ) )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( sk_E
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_D )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['75','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_D )
      | ( sk_E
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( sk_F
       != ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_E
 != ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84','85'])).

thf('92',plain,(
    sk_E
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_D )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( sk_F
       != ( k4_tarski @ ( k1_mcart_1 @ sk_F ) @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( sk_F != sk_F )
    | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_F ) @ sk_D ) ),
    inference('sup-',[status(thm)],['18','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ) )).

thf('96',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k11_mcart_1 @ X24 @ X25 @ X26 @ X27 @ X28 ) @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_mcart_1])).

thf('97',plain,(
    m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_D ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('100',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['100','101','102','103','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_F ) @ sk_D ),
    inference(demod,[status(thm)],['97','105'])).

thf('107',plain,
    ( ( sk_F != sk_F )
    | ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['94','106'])).

thf('108',plain,(
    v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('110',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( ( k4_zfmisc_1 @ X44 @ X45 @ X46 @ X47 )
       != k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('112',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['113','114','115','116','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3rgkz5b2Q1
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.75/1.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.75/1.97  % Solved by: fo/fo7.sh
% 1.75/1.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.97  % done 2173 iterations in 1.516s
% 1.75/1.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.75/1.97  % SZS output start Refutation
% 1.75/1.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.75/1.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.75/1.97  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.75/1.97  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.75/1.97  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.97  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 1.75/1.97  thf(sk_D_type, type, sk_D: $i).
% 1.75/1.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.75/1.97  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.75/1.97  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 1.75/1.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.75/1.97  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.97  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.75/1.97  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 1.75/1.97  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 1.75/1.97  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 1.75/1.97  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.75/1.97  thf(sk_F_type, type, sk_F: $i).
% 1.75/1.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.75/1.97  thf(sk_E_type, type, sk_E: $i).
% 1.75/1.97  thf(sk_C_type, type, sk_C: $i).
% 1.75/1.97  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.75/1.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.75/1.97  thf(t81_mcart_1, conjecture,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.75/1.97     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.75/1.97       ( ( ![G:$i]:
% 1.75/1.97           ( ( m1_subset_1 @ G @ A ) =>
% 1.75/1.97             ( ![H:$i]:
% 1.75/1.97               ( ( m1_subset_1 @ H @ B ) =>
% 1.75/1.97                 ( ![I:$i]:
% 1.75/1.97                   ( ( m1_subset_1 @ I @ C ) =>
% 1.75/1.97                     ( ![J:$i]:
% 1.75/1.97                       ( ( m1_subset_1 @ J @ D ) =>
% 1.75/1.97                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 1.75/1.97                           ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 1.75/1.97         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.97           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 1.75/1.97           ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 1.75/1.97  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.97    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.75/1.97        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.75/1.97          ( ( ![G:$i]:
% 1.75/1.97              ( ( m1_subset_1 @ G @ A ) =>
% 1.75/1.97                ( ![H:$i]:
% 1.75/1.97                  ( ( m1_subset_1 @ H @ B ) =>
% 1.75/1.97                    ( ![I:$i]:
% 1.75/1.97                      ( ( m1_subset_1 @ I @ C ) =>
% 1.75/1.97                        ( ![J:$i]:
% 1.75/1.97                          ( ( m1_subset_1 @ J @ D ) =>
% 1.75/1.97                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 1.75/1.97                              ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 1.75/1.97            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.97              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 1.75/1.97              ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 1.75/1.97    inference('cnf.neg', [status(esa)], [t81_mcart_1])).
% 1.75/1.97  thf('0', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(t2_subset, axiom,
% 1.75/1.97    (![A:$i,B:$i]:
% 1.75/1.97     ( ( m1_subset_1 @ A @ B ) =>
% 1.75/1.97       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.75/1.97  thf('1', plain,
% 1.75/1.97      (![X1 : $i, X2 : $i]:
% 1.75/1.97         ((r2_hidden @ X1 @ X2)
% 1.75/1.97          | (v1_xboole_0 @ X2)
% 1.75/1.97          | ~ (m1_subset_1 @ X1 @ X2))),
% 1.75/1.97      inference('cnf', [status(esa)], [t2_subset])).
% 1.75/1.97  thf('2', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | (r2_hidden @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['0', '1'])).
% 1.75/1.97  thf(t23_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i]:
% 1.75/1.97     ( ( v1_relat_1 @ B ) =>
% 1.75/1.97       ( ( r2_hidden @ A @ B ) =>
% 1.75/1.97         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 1.75/1.97  thf('3', plain,
% 1.75/1.97      (![X42 : $i, X43 : $i]:
% 1.75/1.97         (((X42) = (k4_tarski @ (k1_mcart_1 @ X42) @ (k2_mcart_1 @ X42)))
% 1.75/1.97          | ~ (v1_relat_1 @ X43)
% 1.75/1.97          | ~ (r2_hidden @ X42 @ X43))),
% 1.75/1.97      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.75/1.97  thf('4', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | ~ (v1_relat_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | ((sk_F) = (k4_tarski @ (k1_mcart_1 @ sk_F) @ (k2_mcart_1 @ sk_F))))),
% 1.75/1.97      inference('sup-', [status(thm)], ['2', '3'])).
% 1.75/1.97  thf(d4_zfmisc_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.97     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.75/1.97       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.75/1.97  thf('5', plain,
% 1.75/1.97      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.75/1.97         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 1.75/1.97           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 1.75/1.97      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.97  thf(fc6_relat_1, axiom,
% 1.75/1.97    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.75/1.97  thf('6', plain,
% 1.75/1.97      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.75/1.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.75/1.97  thf('7', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.97         (v1_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))),
% 1.75/1.97      inference('sup+', [status(thm)], ['5', '6'])).
% 1.75/1.97  thf('8', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | ((sk_F) = (k4_tarski @ (k1_mcart_1 @ sk_F) @ (k2_mcart_1 @ sk_F))))),
% 1.75/1.97      inference('demod', [status(thm)], ['4', '7'])).
% 1.75/1.97  thf(l13_xboole_0, axiom,
% 1.75/1.97    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.75/1.97  thf('9', plain,
% 1.75/1.97      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.75/1.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.75/1.97  thf('10', plain,
% 1.75/1.97      ((((sk_F) = (k4_tarski @ (k1_mcart_1 @ sk_F) @ (k2_mcart_1 @ sk_F)))
% 1.75/1.97        | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['8', '9'])).
% 1.75/1.97  thf(t55_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.97     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.75/1.97         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 1.75/1.97       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 1.75/1.97  thf('11', plain,
% 1.75/1.97      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.75/1.97         (((k4_zfmisc_1 @ X44 @ X45 @ X46 @ X47) != (k1_xboole_0))
% 1.75/1.97          | ((X47) = (k1_xboole_0))
% 1.75/1.97          | ((X46) = (k1_xboole_0))
% 1.75/1.97          | ((X45) = (k1_xboole_0))
% 1.75/1.97          | ((X44) = (k1_xboole_0)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.75/1.97  thf('12', plain,
% 1.75/1.97      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.97        | ((sk_F) = (k4_tarski @ (k1_mcart_1 @ sk_F) @ (k2_mcart_1 @ sk_F)))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0))
% 1.75/1.97        | ((sk_B) = (k1_xboole_0))
% 1.75/1.97        | ((sk_C) = (k1_xboole_0))
% 1.75/1.97        | ((sk_D) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.75/1.97  thf('13', plain,
% 1.75/1.97      ((((sk_D) = (k1_xboole_0))
% 1.75/1.97        | ((sk_C) = (k1_xboole_0))
% 1.75/1.97        | ((sk_B) = (k1_xboole_0))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0))
% 1.75/1.97        | ((sk_F) = (k4_tarski @ (k1_mcart_1 @ sk_F) @ (k2_mcart_1 @ sk_F))))),
% 1.75/1.97      inference('simplify', [status(thm)], ['12'])).
% 1.75/1.97  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('17', plain, (((sk_D) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('18', plain,
% 1.75/1.97      (((sk_F) = (k4_tarski @ (k1_mcart_1 @ sk_F) @ (k2_mcart_1 @ sk_F)))),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)],
% 1.75/1.97                ['13', '14', '15', '16', '17'])).
% 1.75/1.97  thf('19', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | (r2_hidden @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['0', '1'])).
% 1.75/1.97  thf('20', plain,
% 1.75/1.97      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.75/1.97         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 1.75/1.97           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 1.75/1.97      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.75/1.97  thf(t10_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i]:
% 1.75/1.97     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.75/1.97       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.75/1.97         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.75/1.97  thf('21', plain,
% 1.75/1.97      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.75/1.97         ((r2_hidden @ (k1_mcart_1 @ X39) @ X40)
% 1.75/1.97          | ~ (r2_hidden @ X39 @ (k2_zfmisc_1 @ X40 @ X41)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.75/1.97  thf('22', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.97         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.75/1.97          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['20', '21'])).
% 1.75/1.97  thf('23', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | (r2_hidden @ (k1_mcart_1 @ sk_F) @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['19', '22'])).
% 1.75/1.97  thf('24', plain,
% 1.75/1.97      (![X42 : $i, X43 : $i]:
% 1.75/1.97         (((X42) = (k4_tarski @ (k1_mcart_1 @ X42) @ (k2_mcart_1 @ X42)))
% 1.75/1.97          | ~ (v1_relat_1 @ X43)
% 1.75/1.97          | ~ (r2_hidden @ X42 @ X43))),
% 1.75/1.97      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.75/1.97  thf('25', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.75/1.97        | ((k1_mcart_1 @ sk_F)
% 1.75/1.97            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)) @ 
% 1.75/1.97               (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 1.75/1.97      inference('sup-', [status(thm)], ['23', '24'])).
% 1.75/1.97  thf(d3_zfmisc_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i]:
% 1.75/1.97     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.75/1.97       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.75/1.97  thf('26', plain,
% 1.75/1.97      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.75/1.97         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 1.75/1.97           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 1.75/1.97      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.97  thf('27', plain,
% 1.75/1.97      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.75/1.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.75/1.97  thf('28', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.97         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 1.75/1.97      inference('sup+', [status(thm)], ['26', '27'])).
% 1.75/1.97  thf('29', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | ((k1_mcart_1 @ sk_F)
% 1.75/1.97            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)) @ 
% 1.75/1.97               (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 1.75/1.97      inference('demod', [status(thm)], ['25', '28'])).
% 1.75/1.97  thf(d3_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i]:
% 1.75/1.97     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.75/1.97  thf('30', plain,
% 1.75/1.97      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.75/1.97         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 1.75/1.97           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 1.75/1.97      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.75/1.97  thf('31', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)) @ 
% 1.75/1.97            (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ X0)
% 1.75/1.97            = (k4_tarski @ (k1_mcart_1 @ sk_F) @ X0))
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 1.75/1.97      inference('sup+', [status(thm)], ['29', '30'])).
% 1.75/1.97  thf('32', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | (r2_hidden @ (k1_mcart_1 @ sk_F) @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['19', '22'])).
% 1.75/1.97  thf('33', plain,
% 1.75/1.97      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.75/1.97         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 1.75/1.97           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 1.75/1.97      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.97  thf('34', plain,
% 1.75/1.97      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.75/1.97         ((r2_hidden @ (k1_mcart_1 @ X39) @ X40)
% 1.75/1.97          | ~ (r2_hidden @ X39 @ (k2_zfmisc_1 @ X40 @ X41)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.75/1.97  thf('35', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.97         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.75/1.97          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['33', '34'])).
% 1.75/1.97  thf('36', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)) @ 
% 1.75/1.97           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['32', '35'])).
% 1.75/1.97  thf('37', plain,
% 1.75/1.97      (![X42 : $i, X43 : $i]:
% 1.75/1.97         (((X42) = (k4_tarski @ (k1_mcart_1 @ X42) @ (k2_mcart_1 @ X42)))
% 1.75/1.97          | ~ (v1_relat_1 @ X43)
% 1.75/1.97          | ~ (r2_hidden @ X42 @ X43))),
% 1.75/1.97      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.75/1.97  thf('38', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.75/1.97        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_F))
% 1.75/1.97            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 1.75/1.97               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))))),
% 1.75/1.97      inference('sup-', [status(thm)], ['36', '37'])).
% 1.75/1.97  thf('39', plain,
% 1.75/1.97      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.75/1.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.75/1.97  thf('40', plain,
% 1.75/1.97      (((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_F))
% 1.75/1.97            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 1.75/1.97               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))))),
% 1.75/1.97      inference('demod', [status(thm)], ['38', '39'])).
% 1.75/1.97  thf('41', plain,
% 1.75/1.97      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.75/1.97         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 1.75/1.97           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 1.75/1.97      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.75/1.97  thf('42', plain,
% 1.75/1.97      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.75/1.97         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 1.75/1.97           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 1.75/1.97      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.75/1.97  thf('43', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.97         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 1.75/1.97           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 1.75/1.97      inference('sup+', [status(thm)], ['41', '42'])).
% 1.75/1.97  thf(d4_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.97     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 1.75/1.97       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 1.75/1.97  thf('44', plain,
% 1.75/1.97      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.75/1.97         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 1.75/1.97           = (k4_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13) @ X14))),
% 1.75/1.97      inference('cnf', [status(esa)], [d4_mcart_1])).
% 1.75/1.97  thf('45', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.97         ((k4_mcart_1 @ X3 @ X2 @ X1 @ X0)
% 1.75/1.97           = (k3_mcart_1 @ (k4_tarski @ X3 @ X2) @ X1 @ X0))),
% 1.75/1.97      inference('sup+', [status(thm)], ['43', '44'])).
% 1.75/1.97  thf('46', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i]:
% 1.75/1.97         (((k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 1.75/1.97            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ X1 @ X0)
% 1.75/1.97            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)) @ X1 @ X0))
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 1.75/1.97      inference('sup+', [status(thm)], ['40', '45'])).
% 1.75/1.97  thf('47', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(dt_k9_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.75/1.97     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.75/1.97       ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ))).
% 1.75/1.97  thf('48', plain,
% 1.75/1.97      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.75/1.97         ((m1_subset_1 @ (k9_mcart_1 @ X34 @ X35 @ X36 @ X37 @ X38) @ X35)
% 1.75/1.97          | ~ (m1_subset_1 @ X38 @ (k4_zfmisc_1 @ X34 @ X35 @ X36 @ X37)))),
% 1.75/1.97      inference('cnf', [status(esa)], [dt_k9_mcart_1])).
% 1.75/1.97  thf('49', plain,
% 1.75/1.97      ((m1_subset_1 @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_B)),
% 1.75/1.97      inference('sup-', [status(thm)], ['47', '48'])).
% 1.75/1.97  thf('50', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(t61_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.97     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.75/1.97          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 1.75/1.97          ( ~( ![E:$i]:
% 1.75/1.97               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.75/1.97                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 1.75/1.97                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 1.75/1.97                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 1.75/1.97                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 1.75/1.97                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 1.75/1.97                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 1.75/1.97                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 1.75/1.97  thf('51', plain,
% 1.75/1.97      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.75/1.97         (((X49) = (k1_xboole_0))
% 1.75/1.97          | ((X50) = (k1_xboole_0))
% 1.75/1.97          | ((X51) = (k1_xboole_0))
% 1.75/1.97          | ((k9_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52)
% 1.75/1.97              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X52))))
% 1.75/1.97          | ~ (m1_subset_1 @ X52 @ (k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53))
% 1.75/1.97          | ((X53) = (k1_xboole_0)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.75/1.97  thf('52', plain,
% 1.75/1.97      ((((sk_D) = (k1_xboole_0))
% 1.75/1.97        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 1.75/1.97            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 1.75/1.97        | ((sk_C) = (k1_xboole_0))
% 1.75/1.97        | ((sk_B) = (k1_xboole_0))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['50', '51'])).
% 1.75/1.97  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('54', plain, (((sk_B) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('56', plain, (((sk_D) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('57', plain,
% 1.75/1.97      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 1.75/1.97         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)],
% 1.75/1.97                ['52', '53', '54', '55', '56'])).
% 1.75/1.97  thf('58', plain,
% 1.75/1.97      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ sk_B)),
% 1.75/1.97      inference('demod', [status(thm)], ['49', '57'])).
% 1.75/1.97  thf('59', plain,
% 1.75/1.97      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 1.75/1.97         (~ (m1_subset_1 @ X54 @ sk_B)
% 1.75/1.97          | ~ (m1_subset_1 @ X55 @ sk_D)
% 1.75/1.97          | ((sk_F) != (k4_mcart_1 @ X56 @ X54 @ X57 @ X55))
% 1.75/1.97          | ((sk_E) = (X57))
% 1.75/1.97          | ~ (m1_subset_1 @ X57 @ sk_C)
% 1.75/1.97          | ~ (m1_subset_1 @ X56 @ sk_A))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('60', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.97         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.75/1.97          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.75/1.97          | ((sk_E) = (X1))
% 1.75/1.97          | ((sk_F)
% 1.75/1.97              != (k4_mcart_1 @ X0 @ 
% 1.75/1.97                  (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ X1 @ X2))
% 1.75/1.97          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 1.75/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.75/1.97  thf('61', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i]:
% 1.75/1.97         (((sk_F)
% 1.75/1.97            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)) @ X1 @ X0))
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ sk_D)
% 1.75/1.97          | ((sk_E) = (X1))
% 1.75/1.97          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.75/1.97          | ~ (m1_subset_1 @ 
% 1.75/1.97               (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ sk_A))),
% 1.75/1.97      inference('sup-', [status(thm)], ['46', '60'])).
% 1.75/1.97  thf('62', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(dt_k8_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.75/1.97     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.75/1.97       ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ))).
% 1.75/1.97  thf('63', plain,
% 1.75/1.97      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.75/1.97         ((m1_subset_1 @ (k8_mcart_1 @ X29 @ X30 @ X31 @ X32 @ X33) @ X29)
% 1.75/1.97          | ~ (m1_subset_1 @ X33 @ (k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32)))),
% 1.75/1.97      inference('cnf', [status(esa)], [dt_k8_mcart_1])).
% 1.75/1.97  thf('64', plain,
% 1.75/1.97      ((m1_subset_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_A)),
% 1.75/1.97      inference('sup-', [status(thm)], ['62', '63'])).
% 1.75/1.97  thf('65', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('66', plain,
% 1.75/1.97      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.75/1.97         (((X49) = (k1_xboole_0))
% 1.75/1.97          | ((X50) = (k1_xboole_0))
% 1.75/1.97          | ((X51) = (k1_xboole_0))
% 1.75/1.97          | ((k8_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52)
% 1.75/1.97              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X52))))
% 1.75/1.97          | ~ (m1_subset_1 @ X52 @ (k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53))
% 1.75/1.97          | ((X53) = (k1_xboole_0)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.75/1.97  thf('67', plain,
% 1.75/1.97      ((((sk_D) = (k1_xboole_0))
% 1.75/1.97        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 1.75/1.97            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 1.75/1.97        | ((sk_C) = (k1_xboole_0))
% 1.75/1.97        | ((sk_B) = (k1_xboole_0))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['65', '66'])).
% 1.75/1.97  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('70', plain, (((sk_C) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('71', plain, (((sk_D) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('72', plain,
% 1.75/1.97      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 1.75/1.97         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)],
% 1.75/1.97                ['67', '68', '69', '70', '71'])).
% 1.75/1.97  thf('73', plain,
% 1.75/1.97      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ sk_A)),
% 1.75/1.97      inference('demod', [status(thm)], ['64', '72'])).
% 1.75/1.97  thf('74', plain,
% 1.75/1.97      (![X0 : $i, X1 : $i]:
% 1.75/1.97         (((sk_F)
% 1.75/1.97            != (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)) @ X1 @ X0))
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ sk_D)
% 1.75/1.97          | ((sk_E) = (X1))
% 1.75/1.97          | ~ (m1_subset_1 @ X1 @ sk_C))),
% 1.75/1.97      inference('demod', [status(thm)], ['61', '73'])).
% 1.75/1.97  thf('75', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (((sk_F) != (k4_tarski @ (k1_mcart_1 @ sk_F) @ X0))
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97          | ~ (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ sk_C)
% 1.75/1.97          | ((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ sk_D)
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['31', '74'])).
% 1.75/1.97  thf('76', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(dt_k10_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.75/1.97     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.75/1.97       ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ))).
% 1.75/1.97  thf('77', plain,
% 1.75/1.97      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.75/1.97         ((m1_subset_1 @ (k10_mcart_1 @ X19 @ X20 @ X21 @ X22 @ X23) @ X21)
% 1.75/1.97          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X22)))),
% 1.75/1.97      inference('cnf', [status(esa)], [dt_k10_mcart_1])).
% 1.75/1.97  thf('78', plain,
% 1.75/1.97      ((m1_subset_1 @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_C)),
% 1.75/1.97      inference('sup-', [status(thm)], ['76', '77'])).
% 1.75/1.97  thf('79', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('80', plain,
% 1.75/1.97      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.75/1.97         (((X49) = (k1_xboole_0))
% 1.75/1.97          | ((X50) = (k1_xboole_0))
% 1.75/1.97          | ((X51) = (k1_xboole_0))
% 1.75/1.97          | ((k10_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52)
% 1.75/1.97              = (k2_mcart_1 @ (k1_mcart_1 @ X52)))
% 1.75/1.97          | ~ (m1_subset_1 @ X52 @ (k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53))
% 1.75/1.97          | ((X53) = (k1_xboole_0)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.75/1.97  thf('81', plain,
% 1.75/1.97      ((((sk_D) = (k1_xboole_0))
% 1.75/1.97        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 1.75/1.97            = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 1.75/1.97        | ((sk_C) = (k1_xboole_0))
% 1.75/1.97        | ((sk_B) = (k1_xboole_0))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['79', '80'])).
% 1.75/1.97  thf('82', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('83', plain, (((sk_B) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('84', plain, (((sk_C) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('85', plain, (((sk_D) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('86', plain,
% 1.75/1.97      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 1.75/1.97         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)],
% 1.75/1.97                ['81', '82', '83', '84', '85'])).
% 1.75/1.97  thf('87', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ sk_C)),
% 1.75/1.97      inference('demod', [status(thm)], ['78', '86'])).
% 1.75/1.97  thf('88', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (((sk_F) != (k4_tarski @ (k1_mcart_1 @ sk_F) @ X0))
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97          | ((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 1.75/1.97          | ~ (m1_subset_1 @ X0 @ sk_D)
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 1.75/1.97      inference('demod', [status(thm)], ['75', '87'])).
% 1.75/1.97  thf('89', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (~ (m1_subset_1 @ X0 @ sk_D)
% 1.75/1.97          | ((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97          | ((sk_F) != (k4_tarski @ (k1_mcart_1 @ sk_F) @ X0)))),
% 1.75/1.97      inference('simplify', [status(thm)], ['88'])).
% 1.75/1.97  thf('90', plain,
% 1.75/1.97      (((sk_E) != (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('91', plain,
% 1.75/1.97      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 1.75/1.97         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)],
% 1.75/1.97                ['81', '82', '83', '84', '85'])).
% 1.75/1.97  thf('92', plain, (((sk_E) != (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 1.75/1.97      inference('demod', [status(thm)], ['90', '91'])).
% 1.75/1.97  thf('93', plain,
% 1.75/1.97      (![X0 : $i]:
% 1.75/1.97         (~ (m1_subset_1 @ X0 @ sk_D)
% 1.75/1.97          | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97          | ((sk_F) != (k4_tarski @ (k1_mcart_1 @ sk_F) @ X0)))),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)], ['89', '92'])).
% 1.75/1.97  thf('94', plain,
% 1.75/1.97      ((((sk_F) != (sk_F))
% 1.75/1.97        | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.75/1.97        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_F) @ sk_D))),
% 1.75/1.97      inference('sup-', [status(thm)], ['18', '93'])).
% 1.75/1.97  thf('95', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf(dt_k11_mcart_1, axiom,
% 1.75/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.75/1.97     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.75/1.97       ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ))).
% 1.75/1.97  thf('96', plain,
% 1.75/1.97      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.75/1.97         ((m1_subset_1 @ (k11_mcart_1 @ X24 @ X25 @ X26 @ X27 @ X28) @ X27)
% 1.75/1.97          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X24 @ X25 @ X26 @ X27)))),
% 1.75/1.97      inference('cnf', [status(esa)], [dt_k11_mcart_1])).
% 1.75/1.97  thf('97', plain,
% 1.75/1.97      ((m1_subset_1 @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_D)),
% 1.75/1.97      inference('sup-', [status(thm)], ['95', '96'])).
% 1.75/1.97  thf('98', plain,
% 1.75/1.97      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('99', plain,
% 1.75/1.97      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.75/1.97         (((X49) = (k1_xboole_0))
% 1.75/1.97          | ((X50) = (k1_xboole_0))
% 1.75/1.97          | ((X51) = (k1_xboole_0))
% 1.75/1.97          | ((k11_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52) = (k2_mcart_1 @ X52))
% 1.75/1.97          | ~ (m1_subset_1 @ X52 @ (k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53))
% 1.75/1.97          | ((X53) = (k1_xboole_0)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.75/1.97  thf('100', plain,
% 1.75/1.97      ((((sk_D) = (k1_xboole_0))
% 1.75/1.97        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 1.75/1.97            = (k2_mcart_1 @ sk_F))
% 1.75/1.97        | ((sk_C) = (k1_xboole_0))
% 1.75/1.97        | ((sk_B) = (k1_xboole_0))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['98', '99'])).
% 1.75/1.97  thf('101', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('102', plain, (((sk_B) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('103', plain, (((sk_C) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('104', plain, (((sk_D) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('105', plain,
% 1.75/1.97      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)],
% 1.75/1.97                ['100', '101', '102', '103', '104'])).
% 1.75/1.97  thf('106', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_F) @ sk_D)),
% 1.75/1.97      inference('demod', [status(thm)], ['97', '105'])).
% 1.75/1.97  thf('107', plain,
% 1.75/1.97      ((((sk_F) != (sk_F))
% 1.75/1.97        | (v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 1.75/1.97      inference('demod', [status(thm)], ['94', '106'])).
% 1.75/1.97  thf('108', plain,
% 1.75/1.97      ((v1_xboole_0 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.75/1.97      inference('simplify', [status(thm)], ['107'])).
% 1.75/1.97  thf('109', plain,
% 1.75/1.97      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.75/1.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.75/1.97  thf('110', plain,
% 1.75/1.97      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.75/1.97      inference('sup-', [status(thm)], ['108', '109'])).
% 1.75/1.97  thf('111', plain,
% 1.75/1.97      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.75/1.97         (((k4_zfmisc_1 @ X44 @ X45 @ X46 @ X47) != (k1_xboole_0))
% 1.75/1.97          | ((X47) = (k1_xboole_0))
% 1.75/1.97          | ((X46) = (k1_xboole_0))
% 1.75/1.97          | ((X45) = (k1_xboole_0))
% 1.75/1.97          | ((X44) = (k1_xboole_0)))),
% 1.75/1.97      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.75/1.97  thf('112', plain,
% 1.75/1.97      ((((k1_xboole_0) != (k1_xboole_0))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0))
% 1.75/1.97        | ((sk_B) = (k1_xboole_0))
% 1.75/1.97        | ((sk_C) = (k1_xboole_0))
% 1.75/1.97        | ((sk_D) = (k1_xboole_0)))),
% 1.75/1.97      inference('sup-', [status(thm)], ['110', '111'])).
% 1.75/1.97  thf('113', plain,
% 1.75/1.97      ((((sk_D) = (k1_xboole_0))
% 1.75/1.97        | ((sk_C) = (k1_xboole_0))
% 1.75/1.97        | ((sk_B) = (k1_xboole_0))
% 1.75/1.97        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.97      inference('simplify', [status(thm)], ['112'])).
% 1.75/1.97  thf('114', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('115', plain, (((sk_B) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('116', plain, (((sk_C) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('117', plain, (((sk_D) != (k1_xboole_0))),
% 1.75/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.97  thf('118', plain, ($false),
% 1.75/1.97      inference('simplify_reflect-', [status(thm)],
% 1.75/1.97                ['113', '114', '115', '116', '117'])).
% 1.75/1.97  
% 1.75/1.97  % SZS output end Refutation
% 1.75/1.97  
% 1.75/1.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
