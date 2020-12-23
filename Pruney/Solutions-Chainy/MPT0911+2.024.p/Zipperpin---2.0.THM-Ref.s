%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B76jwPl8dQ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:59 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  165 (1783 expanded)
%              Number of leaves         :   31 ( 551 expanded)
%              Depth                    :   32
%              Number of atoms          : 1380 (30211 expanded)
%              Number of equality atoms :  186 (3964 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
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
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('12',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
      | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('26',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_mcart_1 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('42',plain,
    ( ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['45','46','47','48'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('51',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X30 @ X29 @ X31 ) )
      | ( sk_D = X31 )
      | ~ ( m1_subset_1 @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['37','53'])).

thf('55',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('57',plain,
    ( ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A_1 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A_1 ),
    inference('simplify_reflect-',[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('66',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','66'])).

thf('68',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('70',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('84',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['68','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A_1 @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C ) ),
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

thf('89',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X25 @ X26 @ X28 @ X27 )
        = ( k2_mcart_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k3_zfmisc_1 @ X25 @ X26 @ X28 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('90',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A_1 @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k7_mcart_1 @ sk_A_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['87','94'])).

thf('96',plain,(
    v1_xboole_0 @ sk_E ),
    inference('simplify_reflect-',[status(thm)],['86','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('98',plain,(
    sk_E = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    sk_E = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('100',plain,(
    sk_E = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('101',plain,(
    sk_E = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('102',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
       != sk_E )
      | ( X23 = sk_E )
      | ( X22 = sk_E )
      | ( X21 = sk_E ) ) ),
    inference(demod,[status(thm)],['25','98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_E )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
      | ( sk_A_1 = sk_E )
      | ( sk_B = sk_E )
      | ( sk_C = sk_E ) ) ),
    inference('sup-',[status(thm)],['24','102'])).

thf('104',plain,
    ( ( sk_C = sk_E )
    | ( sk_B = sk_E )
    | ( sk_A_1 = sk_E )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    v1_xboole_0 @ sk_E ),
    inference('simplify_reflect-',[status(thm)],['86','95'])).

thf('106',plain,
    ( ( sk_C = sk_E )
    | ( sk_B = sk_E )
    | ( sk_A_1 = sk_E )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('simplify_reflect+',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_E = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('109',plain,(
    sk_A_1 != sk_E ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    sk_E = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('112',plain,(
    sk_B != sk_E ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    sk_E = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('115',plain,(
    sk_C != sk_E ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['106','109','112','115'])).

thf('117',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('120',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_mcart_1 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['17','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('129',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( sk_D
    = ( k2_mcart_1 @ sk_E ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['87','94'])).

thf('132',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B76jwPl8dQ
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 1.13/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.35  % Solved by: fo/fo7.sh
% 1.13/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.35  % done 1589 iterations in 0.894s
% 1.13/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.35  % SZS output start Refutation
% 1.13/1.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.13/1.35  thf(sk_D_type, type, sk_D: $i).
% 1.13/1.35  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.13/1.35  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.13/1.35  thf(sk_E_type, type, sk_E: $i).
% 1.13/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.35  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.13/1.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.13/1.35  thf(sk_A_1_type, type, sk_A_1: $i).
% 1.13/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.35  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.13/1.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.13/1.35  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.13/1.35  thf(sk_C_type, type, sk_C: $i).
% 1.13/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.35  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.13/1.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.13/1.35  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.13/1.35  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.13/1.35  thf(t71_mcart_1, conjecture,
% 1.13/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.13/1.35     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.13/1.35       ( ( ![F:$i]:
% 1.13/1.35           ( ( m1_subset_1 @ F @ A ) =>
% 1.13/1.35             ( ![G:$i]:
% 1.13/1.35               ( ( m1_subset_1 @ G @ B ) =>
% 1.13/1.35                 ( ![H:$i]:
% 1.13/1.35                   ( ( m1_subset_1 @ H @ C ) =>
% 1.13/1.35                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.13/1.35                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.13/1.35         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.13/1.35           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.13/1.35           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.13/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.35    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.13/1.35        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.13/1.35          ( ( ![F:$i]:
% 1.13/1.35              ( ( m1_subset_1 @ F @ A ) =>
% 1.13/1.35                ( ![G:$i]:
% 1.13/1.35                  ( ( m1_subset_1 @ G @ B ) =>
% 1.13/1.35                    ( ![H:$i]:
% 1.13/1.35                      ( ( m1_subset_1 @ H @ C ) =>
% 1.13/1.35                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.13/1.35                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.13/1.35            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.13/1.35              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.13/1.35              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.13/1.35    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 1.13/1.35  thf('0', plain,
% 1.13/1.35      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(d2_subset_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( ( v1_xboole_0 @ A ) =>
% 1.13/1.35         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.13/1.35       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.13/1.35         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.13/1.35  thf('1', plain,
% 1.13/1.35      (![X3 : $i, X4 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X3 @ X4)
% 1.13/1.35          | (r2_hidden @ X3 @ X4)
% 1.13/1.35          | (v1_xboole_0 @ X4))),
% 1.13/1.35      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.13/1.35  thf('2', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['0', '1'])).
% 1.13/1.35  thf(t23_mcart_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( v1_relat_1 @ B ) =>
% 1.13/1.35       ( ( r2_hidden @ A @ B ) =>
% 1.13/1.35         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 1.13/1.35  thf('3', plain,
% 1.13/1.35      (![X19 : $i, X20 : $i]:
% 1.13/1.35         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 1.13/1.35          | ~ (v1_relat_1 @ X20)
% 1.13/1.35          | ~ (r2_hidden @ X19 @ X20))),
% 1.13/1.35      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.13/1.35  thf('4', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['2', '3'])).
% 1.13/1.35  thf(d3_zfmisc_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.13/1.35       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.13/1.35  thf('5', plain,
% 1.13/1.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.13/1.35         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 1.13/1.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 1.13/1.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.13/1.35  thf(fc6_relat_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.13/1.35  thf('6', plain,
% 1.13/1.35      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 1.13/1.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.13/1.35  thf('7', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 1.13/1.35      inference('sup+', [status(thm)], ['5', '6'])).
% 1.13/1.35  thf('8', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.13/1.35      inference('demod', [status(thm)], ['4', '7'])).
% 1.13/1.35  thf(l13_xboole_0, axiom,
% 1.13/1.35    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.13/1.35  thf('9', plain,
% 1.13/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.35  thf('10', plain,
% 1.13/1.35      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.13/1.35        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.35  thf(t35_mcart_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.13/1.35         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 1.13/1.35       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 1.13/1.35  thf('11', plain,
% 1.13/1.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.35         (((k3_zfmisc_1 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 1.13/1.35          | ((X23) = (k1_xboole_0))
% 1.13/1.35          | ((X22) = (k1_xboole_0))
% 1.13/1.35          | ((X21) = (k1_xboole_0)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.13/1.35  thf('12', plain,
% 1.13/1.35      ((((k1_xboole_0) != (k1_xboole_0))
% 1.13/1.35        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_C) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['10', '11'])).
% 1.13/1.35  thf('13', plain,
% 1.13/1.35      ((((sk_C) = (k1_xboole_0))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0))
% 1.13/1.35        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.13/1.35      inference('simplify', [status(thm)], ['12'])).
% 1.13/1.35  thf('14', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('17', plain,
% 1.13/1.35      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['13', '14', '15', '16'])).
% 1.13/1.35  thf('18', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['0', '1'])).
% 1.13/1.35  thf('19', plain,
% 1.13/1.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.13/1.35         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 1.13/1.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 1.13/1.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.13/1.35  thf(t10_mcart_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.13/1.35       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.13/1.35         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.13/1.35  thf('20', plain,
% 1.13/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.35         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 1.13/1.35          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.13/1.35  thf('21', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.13/1.35          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['19', '20'])).
% 1.13/1.35  thf('22', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['18', '21'])).
% 1.13/1.35  thf(t8_boole, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.13/1.35  thf('23', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t8_boole])).
% 1.13/1.35  thf('24', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 1.13/1.35          | ((k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C) = (X0))
% 1.13/1.35          | ~ (v1_xboole_0 @ X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['22', '23'])).
% 1.13/1.35  thf('25', plain,
% 1.13/1.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.35         (((k3_zfmisc_1 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 1.13/1.35          | ((X23) = (k1_xboole_0))
% 1.13/1.35          | ((X22) = (k1_xboole_0))
% 1.13/1.35          | ((X21) = (k1_xboole_0)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.13/1.35  thf('26', plain,
% 1.13/1.35      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['13', '14', '15', '16'])).
% 1.13/1.35  thf('27', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['18', '21'])).
% 1.13/1.35  thf('28', plain,
% 1.13/1.35      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('29', plain,
% 1.13/1.35      (![X4 : $i, X5 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X5 @ X4) | (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X4))),
% 1.13/1.35      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.13/1.35  thf('30', plain,
% 1.13/1.35      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | (v1_xboole_0 @ sk_E))),
% 1.13/1.35      inference('sup-', [status(thm)], ['28', '29'])).
% 1.13/1.35  thf('31', plain,
% 1.13/1.35      (((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 1.13/1.35        | (v1_xboole_0 @ sk_E))),
% 1.13/1.35      inference('sup-', [status(thm)], ['27', '30'])).
% 1.13/1.35  thf('32', plain,
% 1.13/1.35      (![X19 : $i, X20 : $i]:
% 1.13/1.35         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 1.13/1.35          | ~ (v1_relat_1 @ X20)
% 1.13/1.35          | ~ (r2_hidden @ X19 @ X20))),
% 1.13/1.35      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.13/1.35  thf('33', plain,
% 1.13/1.35      (((v1_xboole_0 @ sk_E)
% 1.13/1.35        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 1.13/1.35        | ((k1_mcart_1 @ sk_E)
% 1.13/1.35            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.13/1.35               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['31', '32'])).
% 1.13/1.35  thf('34', plain,
% 1.13/1.35      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 1.13/1.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.13/1.35  thf('35', plain,
% 1.13/1.35      (((v1_xboole_0 @ sk_E)
% 1.13/1.35        | ((k1_mcart_1 @ sk_E)
% 1.13/1.35            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.13/1.35               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.13/1.35      inference('demod', [status(thm)], ['33', '34'])).
% 1.13/1.35  thf(d3_mcart_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.13/1.35  thf('36', plain,
% 1.13/1.35      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.13/1.35         ((k3_mcart_1 @ X10 @ X11 @ X12)
% 1.13/1.35           = (k4_tarski @ (k4_tarski @ X10 @ X11) @ X12))),
% 1.13/1.35      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.13/1.35  thf('37', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.13/1.35            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 1.13/1.35            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.13/1.35          | (v1_xboole_0 @ sk_E))),
% 1.13/1.35      inference('sup+', [status(thm)], ['35', '36'])).
% 1.13/1.35  thf('38', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['18', '21'])).
% 1.13/1.35  thf('39', plain,
% 1.13/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.35  thf('40', plain,
% 1.13/1.35      (((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 1.13/1.35        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['38', '39'])).
% 1.13/1.35  thf('41', plain,
% 1.13/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.35         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 1.13/1.35          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.13/1.35  thf('42', plain,
% 1.13/1.35      ((((k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_xboole_0))
% 1.13/1.35        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 1.13/1.35      inference('sup-', [status(thm)], ['40', '41'])).
% 1.13/1.35  thf('43', plain,
% 1.13/1.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.35         (((k3_zfmisc_1 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 1.13/1.35          | ((X23) = (k1_xboole_0))
% 1.13/1.35          | ((X22) = (k1_xboole_0))
% 1.13/1.35          | ((X21) = (k1_xboole_0)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.13/1.35  thf('44', plain,
% 1.13/1.35      ((((k1_xboole_0) != (k1_xboole_0))
% 1.13/1.35        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_C) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['42', '43'])).
% 1.13/1.35  thf('45', plain,
% 1.13/1.35      ((((sk_C) = (k1_xboole_0))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0))
% 1.13/1.35        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 1.13/1.35      inference('simplify', [status(thm)], ['44'])).
% 1.13/1.35  thf('46', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('48', plain, (((sk_C) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('49', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['45', '46', '47', '48'])).
% 1.13/1.35  thf(t1_subset, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.13/1.35  thf('50', plain,
% 1.13/1.35      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.13/1.35      inference('cnf', [status(esa)], [t1_subset])).
% 1.13/1.35  thf('51', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 1.13/1.35      inference('sup-', [status(thm)], ['49', '50'])).
% 1.13/1.35  thf('52', plain,
% 1.13/1.35      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X29 @ sk_B)
% 1.13/1.35          | ((sk_E) != (k3_mcart_1 @ X30 @ X29 @ X31))
% 1.13/1.35          | ((sk_D) = (X31))
% 1.13/1.35          | ~ (m1_subset_1 @ X31 @ sk_C)
% 1.13/1.35          | ~ (m1_subset_1 @ X30 @ sk_A_1))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('53', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X0 @ sk_A_1)
% 1.13/1.35          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.13/1.35          | ((sk_D) = (X1))
% 1.13/1.35          | ((sk_E)
% 1.13/1.35              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['51', '52'])).
% 1.13/1.35  thf('54', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.13/1.35          | (v1_xboole_0 @ sk_E)
% 1.13/1.35          | ((sk_D) = (X0))
% 1.13/1.35          | ~ (m1_subset_1 @ X0 @ sk_C)
% 1.13/1.35          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A_1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['37', '53'])).
% 1.13/1.35  thf('55', plain,
% 1.13/1.35      (((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 1.13/1.35        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['38', '39'])).
% 1.13/1.35  thf('56', plain,
% 1.13/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.35         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 1.13/1.35          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.13/1.35  thf('57', plain,
% 1.13/1.35      ((((k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_xboole_0))
% 1.13/1.35        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A_1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['55', '56'])).
% 1.13/1.35  thf('58', plain,
% 1.13/1.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.35         (((k3_zfmisc_1 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 1.13/1.35          | ((X23) = (k1_xboole_0))
% 1.13/1.35          | ((X22) = (k1_xboole_0))
% 1.13/1.35          | ((X21) = (k1_xboole_0)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.13/1.35  thf('59', plain,
% 1.13/1.35      ((((k1_xboole_0) != (k1_xboole_0))
% 1.13/1.35        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A_1)
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_C) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['57', '58'])).
% 1.13/1.35  thf('60', plain,
% 1.13/1.35      ((((sk_C) = (k1_xboole_0))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0))
% 1.13/1.35        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A_1))),
% 1.13/1.35      inference('simplify', [status(thm)], ['59'])).
% 1.13/1.35  thf('61', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('62', plain, (((sk_B) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('63', plain, (((sk_C) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('64', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A_1)),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['60', '61', '62', '63'])).
% 1.13/1.35  thf('65', plain,
% 1.13/1.35      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.13/1.35      inference('cnf', [status(esa)], [t1_subset])).
% 1.13/1.35  thf('66', plain,
% 1.13/1.35      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A_1)),
% 1.13/1.35      inference('sup-', [status(thm)], ['64', '65'])).
% 1.13/1.35  thf('67', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.13/1.35          | (v1_xboole_0 @ sk_E)
% 1.13/1.35          | ((sk_D) = (X0))
% 1.13/1.35          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 1.13/1.35      inference('demod', [status(thm)], ['54', '66'])).
% 1.13/1.35  thf('68', plain,
% 1.13/1.35      ((((sk_E) != (sk_E))
% 1.13/1.35        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.13/1.35        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.13/1.35        | (v1_xboole_0 @ sk_E))),
% 1.13/1.35      inference('sup-', [status(thm)], ['26', '67'])).
% 1.13/1.35  thf('69', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['0', '1'])).
% 1.13/1.35  thf('70', plain,
% 1.13/1.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.13/1.35         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 1.13/1.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 1.13/1.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.13/1.35  thf('71', plain,
% 1.13/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.35         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 1.13/1.35          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.13/1.35  thf('72', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.13/1.35          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['70', '71'])).
% 1.13/1.35  thf('73', plain,
% 1.13/1.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))
% 1.13/1.35        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.13/1.35      inference('sup-', [status(thm)], ['69', '72'])).
% 1.13/1.35  thf('74', plain,
% 1.13/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.35  thf('75', plain,
% 1.13/1.35      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.13/1.35        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['73', '74'])).
% 1.13/1.35  thf('76', plain,
% 1.13/1.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.35         (((k3_zfmisc_1 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 1.13/1.35          | ((X23) = (k1_xboole_0))
% 1.13/1.35          | ((X22) = (k1_xboole_0))
% 1.13/1.35          | ((X21) = (k1_xboole_0)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.13/1.35  thf('77', plain,
% 1.13/1.35      ((((k1_xboole_0) != (k1_xboole_0))
% 1.13/1.35        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_C) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['75', '76'])).
% 1.13/1.35  thf('78', plain,
% 1.13/1.35      ((((sk_C) = (k1_xboole_0))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0))
% 1.13/1.35        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.13/1.35      inference('simplify', [status(thm)], ['77'])).
% 1.13/1.35  thf('79', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('80', plain, (((sk_B) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('81', plain, (((sk_C) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('82', plain, ((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['78', '79', '80', '81'])).
% 1.13/1.35  thf('83', plain,
% 1.13/1.35      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.13/1.35      inference('cnf', [status(esa)], [t1_subset])).
% 1.13/1.35  thf('84', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.13/1.35      inference('sup-', [status(thm)], ['82', '83'])).
% 1.13/1.35  thf('85', plain,
% 1.13/1.35      ((((sk_E) != (sk_E))
% 1.13/1.35        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.13/1.35        | (v1_xboole_0 @ sk_E))),
% 1.13/1.35      inference('demod', [status(thm)], ['68', '84'])).
% 1.13/1.35  thf('86', plain, (((v1_xboole_0 @ sk_E) | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['85'])).
% 1.13/1.35  thf('87', plain, (((sk_D) != (k7_mcart_1 @ sk_A_1 @ sk_B @ sk_C @ sk_E))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('88', plain,
% 1.13/1.35      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A_1 @ sk_B @ sk_C))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(t50_mcart_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.13/1.35          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.13/1.35          ( ~( ![D:$i]:
% 1.13/1.35               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.13/1.35                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.13/1.35                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.13/1.35                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.13/1.35                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.13/1.35                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.13/1.35  thf('89', plain,
% 1.13/1.35      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.13/1.35         (((X25) = (k1_xboole_0))
% 1.13/1.35          | ((X26) = (k1_xboole_0))
% 1.13/1.35          | ((k7_mcart_1 @ X25 @ X26 @ X28 @ X27) = (k2_mcart_1 @ X27))
% 1.13/1.35          | ~ (m1_subset_1 @ X27 @ (k3_zfmisc_1 @ X25 @ X26 @ X28))
% 1.13/1.35          | ((X28) = (k1_xboole_0)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.13/1.35  thf('90', plain,
% 1.13/1.35      ((((sk_C) = (k1_xboole_0))
% 1.13/1.35        | ((k7_mcart_1 @ sk_A_1 @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 1.13/1.35        | ((sk_B) = (k1_xboole_0))
% 1.13/1.35        | ((sk_A_1) = (k1_xboole_0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['88', '89'])).
% 1.13/1.35  thf('91', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('92', plain, (((sk_B) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('93', plain, (((sk_C) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('94', plain,
% 1.13/1.35      (((k7_mcart_1 @ sk_A_1 @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['90', '91', '92', '93'])).
% 1.13/1.35  thf('95', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 1.13/1.35      inference('demod', [status(thm)], ['87', '94'])).
% 1.13/1.35  thf('96', plain, ((v1_xboole_0 @ sk_E)),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['86', '95'])).
% 1.13/1.35  thf('97', plain,
% 1.13/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.35  thf('98', plain, (((sk_E) = (k1_xboole_0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['96', '97'])).
% 1.13/1.35  thf('99', plain, (((sk_E) = (k1_xboole_0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['96', '97'])).
% 1.13/1.35  thf('100', plain, (((sk_E) = (k1_xboole_0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['96', '97'])).
% 1.13/1.35  thf('101', plain, (((sk_E) = (k1_xboole_0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['96', '97'])).
% 1.13/1.35  thf('102', plain,
% 1.13/1.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.35         (((k3_zfmisc_1 @ X21 @ X22 @ X23) != (sk_E))
% 1.13/1.35          | ((X23) = (sk_E))
% 1.13/1.35          | ((X22) = (sk_E))
% 1.13/1.35          | ((X21) = (sk_E)))),
% 1.13/1.35      inference('demod', [status(thm)], ['25', '98', '99', '100', '101'])).
% 1.13/1.35  thf('103', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (((X0) != (sk_E))
% 1.13/1.35          | ~ (v1_xboole_0 @ X0)
% 1.13/1.35          | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 1.13/1.35          | ((sk_A_1) = (sk_E))
% 1.13/1.35          | ((sk_B) = (sk_E))
% 1.13/1.35          | ((sk_C) = (sk_E)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['24', '102'])).
% 1.13/1.35  thf('104', plain,
% 1.13/1.35      ((((sk_C) = (sk_E))
% 1.13/1.35        | ((sk_B) = (sk_E))
% 1.13/1.35        | ((sk_A_1) = (sk_E))
% 1.13/1.35        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 1.13/1.35        | ~ (v1_xboole_0 @ sk_E))),
% 1.13/1.35      inference('simplify', [status(thm)], ['103'])).
% 1.13/1.35  thf('105', plain, ((v1_xboole_0 @ sk_E)),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['86', '95'])).
% 1.13/1.35  thf('106', plain,
% 1.13/1.35      ((((sk_C) = (sk_E))
% 1.13/1.35        | ((sk_B) = (sk_E))
% 1.13/1.35        | ((sk_A_1) = (sk_E))
% 1.13/1.35        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 1.13/1.35      inference('simplify_reflect+', [status(thm)], ['104', '105'])).
% 1.13/1.35  thf('107', plain, (((sk_A_1) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('108', plain, (((sk_E) = (k1_xboole_0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['96', '97'])).
% 1.13/1.35  thf('109', plain, (((sk_A_1) != (sk_E))),
% 1.13/1.35      inference('demod', [status(thm)], ['107', '108'])).
% 1.13/1.35  thf('110', plain, (((sk_B) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('111', plain, (((sk_E) = (k1_xboole_0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['96', '97'])).
% 1.13/1.35  thf('112', plain, (((sk_B) != (sk_E))),
% 1.13/1.35      inference('demod', [status(thm)], ['110', '111'])).
% 1.13/1.35  thf('113', plain, (((sk_C) != (k1_xboole_0))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('114', plain, (((sk_E) = (k1_xboole_0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['96', '97'])).
% 1.13/1.35  thf('115', plain, (((sk_C) != (sk_E))),
% 1.13/1.35      inference('demod', [status(thm)], ['113', '114'])).
% 1.13/1.35  thf('116', plain,
% 1.13/1.35      ((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)],
% 1.13/1.35                ['106', '109', '112', '115'])).
% 1.13/1.35  thf('117', plain,
% 1.13/1.35      (![X19 : $i, X20 : $i]:
% 1.13/1.35         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 1.13/1.35          | ~ (v1_relat_1 @ X20)
% 1.13/1.35          | ~ (r2_hidden @ X19 @ X20))),
% 1.13/1.35      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.13/1.35  thf('118', plain,
% 1.13/1.35      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 1.13/1.35        | ((k1_mcart_1 @ sk_E)
% 1.13/1.35            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.13/1.35               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['116', '117'])).
% 1.13/1.35  thf('119', plain,
% 1.13/1.35      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 1.13/1.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.13/1.35  thf('120', plain,
% 1.13/1.35      (((k1_mcart_1 @ sk_E)
% 1.13/1.35         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.13/1.35            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 1.13/1.35      inference('demod', [status(thm)], ['118', '119'])).
% 1.13/1.35  thf('121', plain,
% 1.13/1.35      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.13/1.35         ((k3_mcart_1 @ X10 @ X11 @ X12)
% 1.13/1.35           = (k4_tarski @ (k4_tarski @ X10 @ X11) @ X12))),
% 1.13/1.35      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.13/1.35  thf('122', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.13/1.35           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 1.13/1.35           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 1.13/1.35      inference('sup+', [status(thm)], ['120', '121'])).
% 1.13/1.35  thf('123', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X0 @ sk_A_1)
% 1.13/1.35          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.13/1.35          | ((sk_D) = (X1))
% 1.13/1.35          | ((sk_E)
% 1.13/1.35              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['51', '52'])).
% 1.13/1.35  thf('124', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.13/1.35          | ((sk_D) = (X0))
% 1.13/1.35          | ~ (m1_subset_1 @ X0 @ sk_C)
% 1.13/1.35          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A_1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['122', '123'])).
% 1.13/1.35  thf('125', plain,
% 1.13/1.35      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A_1)),
% 1.13/1.35      inference('sup-', [status(thm)], ['64', '65'])).
% 1.13/1.35  thf('126', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.13/1.35          | ((sk_D) = (X0))
% 1.13/1.35          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 1.13/1.35      inference('demod', [status(thm)], ['124', '125'])).
% 1.13/1.35  thf('127', plain,
% 1.13/1.35      ((((sk_E) != (sk_E))
% 1.13/1.35        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.13/1.35        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['17', '126'])).
% 1.13/1.35  thf('128', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.13/1.35      inference('sup-', [status(thm)], ['82', '83'])).
% 1.13/1.35  thf('129', plain, ((((sk_E) != (sk_E)) | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 1.13/1.35      inference('demod', [status(thm)], ['127', '128'])).
% 1.13/1.35  thf('130', plain, (((sk_D) = (k2_mcart_1 @ sk_E))),
% 1.13/1.35      inference('simplify', [status(thm)], ['129'])).
% 1.13/1.35  thf('131', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 1.13/1.35      inference('demod', [status(thm)], ['87', '94'])).
% 1.13/1.35  thf('132', plain, ($false),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 1.13/1.35  
% 1.13/1.35  % SZS output end Refutation
% 1.13/1.35  
% 1.13/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
