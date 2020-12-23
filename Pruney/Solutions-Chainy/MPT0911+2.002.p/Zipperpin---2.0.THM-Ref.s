%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QpO2DQWNm8

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:55 EST 2020

% Result     : Theorem 4.84s
% Output     : Refutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  292 (2329 expanded)
%              Number of leaves         :   49 ( 743 expanded)
%              Depth                    :   32
%              Number of atoms          : 2578 (28224 expanded)
%              Number of equality atoms :  341 (3653 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_zfmisc_1 @ X40 @ X41 @ X42 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X19 ) @ ( sk_E @ X19 ) )
        = X19 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('sup-',[status(thm)],['2','5'])).

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

thf('7',plain,(
    ! [X50: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X50 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 )
      | ( ( k4_xboole_0 @ X0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X59: $i,X60: $i,X61: $i,X63: $i] :
      ( ( X63 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X63 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('19',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('20',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('21',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_zfmisc_1 @ X40 @ X41 @ X42 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X1 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_zfmisc_1 @ X40 @ X41 @ X42 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_zfmisc_1 @ X40 @ X41 @ X42 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X59: $i,X60: $i,X61: $i,X63: $i] :
      ( ( X59 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X63 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('32',plain,(
    ! [X60: $i,X61: $i,X63: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X60 @ X61 @ X63 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['12','34'])).

thf('36',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( k1_xboole_0 != sk_E_1 )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(eq_fact,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('47',plain,
    ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
    = sk_E_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
    = sk_E_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('49',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X64 @ X65 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('50',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( sk_D @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
    = sk_E_1 ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
    = sk_E_1 ),
    inference(demod,[status(thm)],['47','50'])).

thf('53',plain,(
    ! [X64: $i,X66: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X64 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('54',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_E @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) )
    = sk_E_1 ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('57',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_zfmisc_1 @ X40 @ X41 @ X42 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('58',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X19 ) @ ( sk_E @ X19 ) )
        = X19 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('64',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X64 @ X65 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('65',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('67',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30','32'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(condensation,[status(thm)],['81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['62','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('85',plain,(
    ! [X64: $i,X66: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X64 @ X66 ) )
      = X66 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('86',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('88',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30','32'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['95','96','97','98'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(condensation,[status(thm)],['102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['83','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('106',plain,
    ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30','32'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30','32'])).

thf('119',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('120',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30','32'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('125',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('127',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('129',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('130',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('137',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('138',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('139',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('140',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X3: $i] :
      ( ~ ( r2_hidden @ X3 @ k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','142'])).

thf(t3_ordinal1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ B @ C )
        & ( r2_hidden @ C @ A ) ) )).

thf('144',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( r2_hidden @ X36 @ X34 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_ordinal1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ k1_xboole_0 @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','147'])).

thf('149',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup+',[status(thm)],['117','149'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('151',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('152',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    = ( k1_mcart_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('153',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_mcart_1 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('156',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('157',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 )
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','33'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['148'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('178',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ sk_B_2 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X68 @ X67 @ X69 ) )
      | ( sk_D_1 = X69 )
      | ~ ( m1_subset_1 @ X69 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X68 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_2 )
      | ( sk_D_1 = X1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','180'])).

thf('182',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('183',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('184',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 )
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','33'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['193','194','195','196'])).

thf('198',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('201',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['148'])).

thf('203',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['181','203'])).

thf('205',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['55','204'])).

thf('206',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('207',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_zfmisc_1 @ X40 @ X41 @ X42 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('208',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('209',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['206','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 )
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','33'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( ( k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62 )
       != k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['219','220','221','222'])).

thf('224',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['148'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('229',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['205','229'])).

thf('231',plain,
    ( sk_D_1
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ),
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

thf('234',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X55 @ X56 @ X58 @ X57 )
        = ( k2_mcart_1 @ X57 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k3_zfmisc_1 @ X55 @ X56 @ X58 ) )
      | ( X58 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('235',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['235','236','237','238'])).

thf('240',plain,(
    sk_D_1
 != ( k2_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['232','239'])).

thf('241',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['231','240'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QpO2DQWNm8
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.84/5.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.84/5.08  % Solved by: fo/fo7.sh
% 4.84/5.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.84/5.08  % done 6085 iterations in 4.626s
% 4.84/5.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.84/5.08  % SZS output start Refutation
% 4.84/5.08  thf(sk_E_type, type, sk_E: $i > $i).
% 4.84/5.08  thf(sk_B_type, type, sk_B: $i > $i).
% 4.84/5.08  thf(sk_D_type, type, sk_D: $i > $i).
% 4.84/5.08  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 4.84/5.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.84/5.08  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 4.84/5.08  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 4.84/5.08  thf(sk_B_2_type, type, sk_B_2: $i).
% 4.84/5.08  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 4.84/5.08  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 4.84/5.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.84/5.08  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 4.84/5.08  thf(sk_A_type, type, sk_A: $i).
% 4.84/5.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.84/5.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.84/5.08  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 4.84/5.08  thf(sk_D_1_type, type, sk_D_1: $i).
% 4.84/5.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.84/5.08  thf(sk_E_1_type, type, sk_E_1: $i).
% 4.84/5.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.84/5.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.84/5.08  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 4.84/5.08  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.84/5.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.84/5.08  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 4.84/5.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.84/5.08  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.84/5.08  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 4.84/5.08  thf(t71_mcart_1, conjecture,
% 4.84/5.08    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.84/5.08     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 4.84/5.08       ( ( ![F:$i]:
% 4.84/5.08           ( ( m1_subset_1 @ F @ A ) =>
% 4.84/5.08             ( ![G:$i]:
% 4.84/5.08               ( ( m1_subset_1 @ G @ B ) =>
% 4.84/5.08                 ( ![H:$i]:
% 4.84/5.08                   ( ( m1_subset_1 @ H @ C ) =>
% 4.84/5.08                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 4.84/5.08                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 4.84/5.08         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.84/5.08           ( ( C ) = ( k1_xboole_0 ) ) | 
% 4.84/5.08           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 4.84/5.08  thf(zf_stmt_0, negated_conjecture,
% 4.84/5.08    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.84/5.08        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 4.84/5.08          ( ( ![F:$i]:
% 4.84/5.08              ( ( m1_subset_1 @ F @ A ) =>
% 4.84/5.08                ( ![G:$i]:
% 4.84/5.08                  ( ( m1_subset_1 @ G @ B ) =>
% 4.84/5.08                    ( ![H:$i]:
% 4.84/5.08                      ( ( m1_subset_1 @ H @ C ) =>
% 4.84/5.08                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 4.84/5.08                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 4.84/5.08            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.84/5.08              ( ( C ) = ( k1_xboole_0 ) ) | 
% 4.84/5.08              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 4.84/5.08    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 4.84/5.08  thf('0', plain,
% 4.84/5.08      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf(t2_subset, axiom,
% 4.84/5.08    (![A:$i,B:$i]:
% 4.84/5.08     ( ( m1_subset_1 @ A @ B ) =>
% 4.84/5.08       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 4.84/5.08  thf('1', plain,
% 4.84/5.08      (![X29 : $i, X30 : $i]:
% 4.84/5.08         ((r2_hidden @ X29 @ X30)
% 4.84/5.08          | (v1_xboole_0 @ X30)
% 4.84/5.08          | ~ (m1_subset_1 @ X29 @ X30))),
% 4.84/5.08      inference('cnf', [status(esa)], [t2_subset])).
% 4.84/5.08  thf('2', plain,
% 4.84/5.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.08        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['0', '1'])).
% 4.84/5.08  thf(d3_zfmisc_1, axiom,
% 4.84/5.08    (![A:$i,B:$i,C:$i]:
% 4.84/5.08     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 4.84/5.08       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 4.84/5.08  thf('3', plain,
% 4.84/5.08      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ X40 @ X41 @ X42)
% 4.84/5.08           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41) @ X42))),
% 4.84/5.08      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.84/5.08  thf(l139_zfmisc_1, axiom,
% 4.84/5.08    (![A:$i,B:$i,C:$i]:
% 4.84/5.08     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 4.84/5.08          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 4.84/5.08  thf('4', plain,
% 4.84/5.08      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.84/5.08         (((k4_tarski @ (sk_D @ X19) @ (sk_E @ X19)) = (X19))
% 4.84/5.08          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 4.84/5.08      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 4.84/5.08  thf('5', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.84/5.08         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 4.84/5.08          | ((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['3', '4'])).
% 4.84/5.08  thf('6', plain,
% 4.84/5.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.08        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['2', '5'])).
% 4.84/5.08  thf(t34_mcart_1, axiom,
% 4.84/5.08    (![A:$i]:
% 4.84/5.08     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.84/5.08          ( ![B:$i]:
% 4.84/5.08            ( ~( ( r2_hidden @ B @ A ) & 
% 4.84/5.08                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 4.84/5.08                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 4.84/5.08                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 4.84/5.08  thf('7', plain,
% 4.84/5.08      (![X50 : $i]:
% 4.84/5.08         (((X50) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X50) @ X50))),
% 4.84/5.08      inference('cnf', [status(esa)], [t34_mcart_1])).
% 4.84/5.08  thf(d1_xboole_0, axiom,
% 4.84/5.08    (![A:$i]:
% 4.84/5.08     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.84/5.08  thf('8', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.84/5.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.84/5.08  thf('9', plain,
% 4.84/5.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.84/5.08      inference('sup-', [status(thm)], ['7', '8'])).
% 4.84/5.08  thf(t3_boole, axiom,
% 4.84/5.08    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.84/5.08  thf('10', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 4.84/5.08      inference('cnf', [status(esa)], [t3_boole])).
% 4.84/5.08  thf('11', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i]:
% 4.84/5.08         (((k4_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 4.84/5.08      inference('sup+', [status(thm)], ['9', '10'])).
% 4.84/5.08  thf('12', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 4.84/5.08          | ((k4_xboole_0 @ X0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2)) = (X0)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['6', '11'])).
% 4.84/5.08  thf('13', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 4.84/5.08      inference('cnf', [status(esa)], [t3_boole])).
% 4.84/5.08  thf(t48_xboole_1, axiom,
% 4.84/5.08    (![A:$i,B:$i]:
% 4.84/5.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.84/5.08  thf('14', plain,
% 4.84/5.08      (![X17 : $i, X18 : $i]:
% 4.84/5.08         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 4.84/5.08           = (k3_xboole_0 @ X17 @ X18))),
% 4.84/5.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.84/5.08  thf('15', plain,
% 4.84/5.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 4.84/5.08      inference('sup+', [status(thm)], ['13', '14'])).
% 4.84/5.08  thf(t2_boole, axiom,
% 4.84/5.08    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 4.84/5.08  thf('16', plain,
% 4.84/5.08      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [t2_boole])).
% 4.84/5.08  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.84/5.08      inference('demod', [status(thm)], ['15', '16'])).
% 4.84/5.08  thf(t55_mcart_1, axiom,
% 4.84/5.08    (![A:$i,B:$i,C:$i,D:$i]:
% 4.84/5.08     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 4.84/5.08         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 4.84/5.08       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 4.84/5.08  thf('18', plain,
% 4.84/5.08      (![X59 : $i, X60 : $i, X61 : $i, X63 : $i]:
% 4.84/5.08         (((X63) != (k1_xboole_0))
% 4.84/5.08          | ((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X63) = (k1_xboole_0)))),
% 4.84/5.08      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.08  thf('19', plain,
% 4.84/5.08      (![X59 : $i, X60 : $i, X61 : $i]:
% 4.84/5.08         ((k4_zfmisc_1 @ X59 @ X60 @ X61 @ k1_xboole_0) = (k1_xboole_0))),
% 4.84/5.08      inference('simplify', [status(thm)], ['18'])).
% 4.84/5.08  thf(d4_zfmisc_1, axiom,
% 4.84/5.08    (![A:$i,B:$i,C:$i,D:$i]:
% 4.84/5.08     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 4.84/5.08       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 4.84/5.08  thf('20', plain,
% 4.84/5.08      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.08         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.08           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.08      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.08  thf('21', plain,
% 4.84/5.08      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ X40 @ X41 @ X42)
% 4.84/5.08           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41) @ X42))),
% 4.84/5.08      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.84/5.08  thf('22', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 4.84/5.08           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 4.84/5.08      inference('sup+', [status(thm)], ['20', '21'])).
% 4.84/5.08  thf('23', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ k1_xboole_0 @ X0)
% 4.84/5.08           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 4.84/5.08      inference('sup+', [status(thm)], ['19', '22'])).
% 4.84/5.08  thf('24', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ k1_xboole_0 @ X0)
% 4.84/5.08           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 4.84/5.08      inference('sup+', [status(thm)], ['19', '22'])).
% 4.84/5.08  thf('25', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ X1)
% 4.84/5.08           = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 4.84/5.08      inference('sup+', [status(thm)], ['23', '24'])).
% 4.84/5.08  thf('26', plain,
% 4.84/5.08      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ X40 @ X41 @ X42)
% 4.84/5.08           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41) @ X42))),
% 4.84/5.08      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.84/5.08  thf('27', plain,
% 4.84/5.08      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ X40 @ X41 @ X42)
% 4.84/5.08           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41) @ X42))),
% 4.84/5.08      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.84/5.08  thf('28', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 4.84/5.08           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 4.84/5.08      inference('sup+', [status(thm)], ['26', '27'])).
% 4.84/5.08  thf('29', plain,
% 4.84/5.08      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.08         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.08           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.08      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.08  thf('30', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 4.84/5.08           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 4.84/5.08      inference('demod', [status(thm)], ['28', '29'])).
% 4.84/5.08  thf('31', plain,
% 4.84/5.08      (![X59 : $i, X60 : $i, X61 : $i, X63 : $i]:
% 4.84/5.08         (((X59) != (k1_xboole_0))
% 4.84/5.08          | ((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X63) = (k1_xboole_0)))),
% 4.84/5.08      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.08  thf('32', plain,
% 4.84/5.08      (![X60 : $i, X61 : $i, X63 : $i]:
% 4.84/5.08         ((k4_zfmisc_1 @ k1_xboole_0 @ X60 @ X61 @ X63) = (k1_xboole_0))),
% 4.84/5.08      inference('simplify', [status(thm)], ['31'])).
% 4.84/5.08  thf('33', plain,
% 4.84/5.08      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 4.84/5.08      inference('demod', [status(thm)], ['25', '30', '32'])).
% 4.84/5.08  thf('34', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i]:
% 4.84/5.08         ((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 4.84/5.08      inference('sup+', [status(thm)], ['17', '33'])).
% 4.84/5.08  thf('35', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k1_xboole_0)
% 4.84/5.08            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) @ X0))
% 4.84/5.08          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 4.84/5.08      inference('sup+', [status(thm)], ['12', '34'])).
% 4.84/5.08  thf('36', plain,
% 4.84/5.08      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.08         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.08           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.08      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.08  thf('37', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0))
% 4.84/5.08          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 4.84/5.08      inference('demod', [status(thm)], ['35', '36'])).
% 4.84/5.08  thf('38', plain,
% 4.84/5.08      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 4.84/5.08         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 4.84/5.08          | ((X62) = (k1_xboole_0))
% 4.84/5.08          | ((X61) = (k1_xboole_0))
% 4.84/5.08          | ((X60) = (k1_xboole_0))
% 4.84/5.08          | ((X59) = (k1_xboole_0)))),
% 4.84/5.08      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.08  thf('39', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k1_xboole_0) != (k1_xboole_0))
% 4.84/5.08          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 4.84/5.08          | ((sk_A) = (k1_xboole_0))
% 4.84/5.08          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.08          | ((X0) = (k1_xboole_0)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['37', '38'])).
% 4.84/5.08  thf('40', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_A) = (k1_xboole_0))
% 4.84/5.08          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 4.84/5.08      inference('simplify', [status(thm)], ['39'])).
% 4.84/5.08  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('42', plain, (((sk_B_2) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('43', plain, (((sk_C_2) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('44', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 4.84/5.08      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 4.84/5.08  thf('45', plain,
% 4.84/5.08      ((((k1_xboole_0) != (sk_E_1))
% 4.84/5.08        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 4.84/5.08      inference('eq_fact', [status(thm)], ['44'])).
% 4.84/5.08  thf('46', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 4.84/5.08      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 4.84/5.08  thf('47', plain,
% 4.84/5.08      (((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))),
% 4.84/5.08      inference('clc', [status(thm)], ['45', '46'])).
% 4.84/5.08  thf('48', plain,
% 4.84/5.08      (((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))),
% 4.84/5.08      inference('clc', [status(thm)], ['45', '46'])).
% 4.84/5.08  thf(t7_mcart_1, axiom,
% 4.84/5.08    (![A:$i,B:$i]:
% 4.84/5.08     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 4.84/5.08       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 4.84/5.08  thf('49', plain,
% 4.84/5.08      (![X64 : $i, X65 : $i]: ((k1_mcart_1 @ (k4_tarski @ X64 @ X65)) = (X64))),
% 4.84/5.08      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.84/5.08  thf('50', plain, (((k1_mcart_1 @ sk_E_1) = (sk_D @ sk_E_1))),
% 4.84/5.08      inference('sup+', [status(thm)], ['48', '49'])).
% 4.84/5.08  thf('51', plain,
% 4.84/5.08      (((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))),
% 4.84/5.08      inference('demod', [status(thm)], ['47', '50'])).
% 4.84/5.08  thf('52', plain,
% 4.84/5.08      (((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))),
% 4.84/5.08      inference('demod', [status(thm)], ['47', '50'])).
% 4.84/5.08  thf('53', plain,
% 4.84/5.08      (![X64 : $i, X66 : $i]: ((k2_mcart_1 @ (k4_tarski @ X64 @ X66)) = (X66))),
% 4.84/5.08      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.84/5.08  thf('54', plain, (((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))),
% 4.84/5.08      inference('sup+', [status(thm)], ['52', '53'])).
% 4.84/5.08  thf('55', plain,
% 4.84/5.08      (((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)) = (sk_E_1))),
% 4.84/5.08      inference('demod', [status(thm)], ['51', '54'])).
% 4.84/5.08  thf('56', plain,
% 4.84/5.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.08        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['0', '1'])).
% 4.84/5.08  thf('57', plain,
% 4.84/5.08      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.84/5.08         ((k3_zfmisc_1 @ X40 @ X41 @ X42)
% 4.84/5.08           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41) @ X42))),
% 4.84/5.08      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.84/5.08  thf(t10_mcart_1, axiom,
% 4.84/5.08    (![A:$i,B:$i,C:$i]:
% 4.84/5.08     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 4.84/5.08       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 4.84/5.08         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 4.84/5.08  thf('58', plain,
% 4.84/5.08      (![X47 : $i, X48 : $i, X49 : $i]:
% 4.84/5.08         ((r2_hidden @ (k1_mcart_1 @ X47) @ X48)
% 4.84/5.08          | ~ (r2_hidden @ X47 @ (k2_zfmisc_1 @ X48 @ X49)))),
% 4.84/5.08      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.84/5.08  thf('59', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.84/5.08         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 4.84/5.08          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['57', '58'])).
% 4.84/5.08  thf('60', plain,
% 4.84/5.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.08        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['56', '59'])).
% 4.84/5.08  thf('61', plain,
% 4.84/5.08      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.84/5.08         (((k4_tarski @ (sk_D @ X19) @ (sk_E @ X19)) = (X19))
% 4.84/5.08          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 4.84/5.08      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 4.84/5.08  thf('62', plain,
% 4.84/5.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.08        | ((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.08            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['60', '61'])).
% 4.84/5.08  thf('63', plain,
% 4.84/5.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.08        | ((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.08            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['60', '61'])).
% 4.84/5.08  thf('64', plain,
% 4.84/5.08      (![X64 : $i, X65 : $i]: ((k1_mcart_1 @ (k4_tarski @ X64 @ X65)) = (X64))),
% 4.84/5.08      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.84/5.08  thf('65', plain,
% 4.84/5.08      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2)))),
% 4.84/5.08      inference('sup+', [status(thm)], ['63', '64'])).
% 4.84/5.08  thf('66', plain,
% 4.84/5.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.84/5.08      inference('sup-', [status(thm)], ['7', '8'])).
% 4.84/5.08  thf('67', plain,
% 4.84/5.08      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k1_xboole_0)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['65', '66'])).
% 4.84/5.08  thf('68', plain,
% 4.84/5.08      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.08         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.08           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.08      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.08  thf('69', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0)
% 4.84/5.08            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 4.84/5.08          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('sup+', [status(thm)], ['67', '68'])).
% 4.84/5.08  thf('70', plain,
% 4.84/5.08      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 4.84/5.08      inference('demod', [status(thm)], ['25', '30', '32'])).
% 4.84/5.08  thf('71', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0) = (k1_xboole_0))
% 4.84/5.08          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('demod', [status(thm)], ['69', '70'])).
% 4.84/5.08  thf('72', plain,
% 4.84/5.08      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 4.84/5.08         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 4.84/5.08          | ((X62) = (k1_xboole_0))
% 4.84/5.08          | ((X61) = (k1_xboole_0))
% 4.84/5.08          | ((X60) = (k1_xboole_0))
% 4.84/5.08          | ((X59) = (k1_xboole_0)))),
% 4.84/5.08      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.08  thf('73', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k1_xboole_0) != (k1_xboole_0))
% 4.84/5.08          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08          | ((sk_A) = (k1_xboole_0))
% 4.84/5.08          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.08          | ((X0) = (k1_xboole_0)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['71', '72'])).
% 4.84/5.08  thf('74', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_A) = (k1_xboole_0))
% 4.84/5.08          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('simplify', [status(thm)], ['73'])).
% 4.84/5.08  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('76', plain, (((sk_B_2) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('77', plain, (((sk_C_2) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('78', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 4.84/5.08  thf('79', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 4.84/5.08  thf('80', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i]:
% 4.84/5.08         (((X1) = (X0))
% 4.84/5.08          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('sup+', [status(thm)], ['78', '79'])).
% 4.84/5.08  thf('81', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i]:
% 4.84/5.08         (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08            = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08          | ((X1) = (X0)))),
% 4.84/5.08      inference('simplify', [status(thm)], ['80'])).
% 4.84/5.08  thf('82', plain,
% 4.84/5.08      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.08      inference('condensation', [status(thm)], ['81'])).
% 4.84/5.08  thf('83', plain,
% 4.84/5.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.08        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.08            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.08      inference('demod', [status(thm)], ['62', '82'])).
% 4.84/5.08  thf('84', plain,
% 4.84/5.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.08        | ((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.08            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['60', '61'])).
% 4.84/5.08  thf('85', plain,
% 4.84/5.08      (![X64 : $i, X66 : $i]: ((k2_mcart_1 @ (k4_tarski @ X64 @ X66)) = (X66))),
% 4.84/5.08      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.84/5.08  thf('86', plain,
% 4.84/5.08      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2)))),
% 4.84/5.08      inference('sup+', [status(thm)], ['84', '85'])).
% 4.84/5.08  thf('87', plain,
% 4.84/5.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.84/5.08      inference('sup-', [status(thm)], ['7', '8'])).
% 4.84/5.08  thf('88', plain,
% 4.84/5.08      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k1_xboole_0)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['86', '87'])).
% 4.84/5.08  thf('89', plain,
% 4.84/5.08      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.08         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.08           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.08      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.08  thf('90', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0)
% 4.84/5.08            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 4.84/5.08          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('sup+', [status(thm)], ['88', '89'])).
% 4.84/5.08  thf('91', plain,
% 4.84/5.08      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 4.84/5.08      inference('demod', [status(thm)], ['25', '30', '32'])).
% 4.84/5.08  thf('92', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0) = (k1_xboole_0))
% 4.84/5.08          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('demod', [status(thm)], ['90', '91'])).
% 4.84/5.08  thf('93', plain,
% 4.84/5.08      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 4.84/5.08         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 4.84/5.08          | ((X62) = (k1_xboole_0))
% 4.84/5.08          | ((X61) = (k1_xboole_0))
% 4.84/5.08          | ((X60) = (k1_xboole_0))
% 4.84/5.08          | ((X59) = (k1_xboole_0)))),
% 4.84/5.08      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.08  thf('94', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((k1_xboole_0) != (k1_xboole_0))
% 4.84/5.08          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08          | ((sk_A) = (k1_xboole_0))
% 4.84/5.08          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.08          | ((X0) = (k1_xboole_0)))),
% 4.84/5.08      inference('sup-', [status(thm)], ['92', '93'])).
% 4.84/5.08  thf('95', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.08          | ((sk_A) = (k1_xboole_0))
% 4.84/5.08          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('simplify', [status(thm)], ['94'])).
% 4.84/5.08  thf('96', plain, (((sk_A) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('97', plain, (((sk_B_2) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('98', plain, (((sk_C_2) != (k1_xboole_0))),
% 4.84/5.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.08  thf('99', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('simplify_reflect-', [status(thm)], ['95', '96', '97', '98'])).
% 4.84/5.08  thf('100', plain,
% 4.84/5.08      (![X0 : $i]:
% 4.84/5.08         (((X0) = (k1_xboole_0))
% 4.84/5.08          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.08      inference('simplify_reflect-', [status(thm)], ['95', '96', '97', '98'])).
% 4.84/5.08  thf('101', plain,
% 4.84/5.08      (![X0 : $i, X1 : $i]:
% 4.84/5.08         (((X1) = (X0))
% 4.84/5.08          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.08          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.08              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 4.84/5.09      inference('sup+', [status(thm)], ['99', '100'])).
% 4.84/5.09  thf('102', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 4.84/5.09            = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 4.84/5.09          | ((X1) = (X0)))),
% 4.84/5.09      inference('simplify', [status(thm)], ['101'])).
% 4.84/5.09  thf('103', plain,
% 4.84/5.09      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('condensation', [status(thm)], ['102'])).
% 4.84/5.09  thf('104', plain,
% 4.84/5.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.09        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('demod', [status(thm)], ['83', '103'])).
% 4.84/5.09  thf('105', plain,
% 4.84/5.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['7', '8'])).
% 4.84/5.09  thf('106', plain,
% 4.84/5.09      ((((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09          (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 4.84/5.09        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k1_xboole_0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['104', '105'])).
% 4.84/5.09  thf('107', plain,
% 4.84/5.09      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.09         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.09           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.09      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.09  thf('108', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0)
% 4.84/5.09            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 4.84/5.09          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('sup+', [status(thm)], ['106', '107'])).
% 4.84/5.09  thf('109', plain,
% 4.84/5.09      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 4.84/5.09      inference('demod', [status(thm)], ['25', '30', '32'])).
% 4.84/5.09  thf('110', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0) = (k1_xboole_0))
% 4.84/5.09          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('demod', [status(thm)], ['108', '109'])).
% 4.84/5.09  thf('111', plain,
% 4.84/5.09      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 4.84/5.09         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 4.84/5.09          | ((X62) = (k1_xboole_0))
% 4.84/5.09          | ((X61) = (k1_xboole_0))
% 4.84/5.09          | ((X60) = (k1_xboole_0))
% 4.84/5.09          | ((X59) = (k1_xboole_0)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.09  thf('112', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0) != (k1_xboole_0))
% 4.84/5.09          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 4.84/5.09          | ((sk_A) = (k1_xboole_0))
% 4.84/5.09          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.09          | ((X0) = (k1_xboole_0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['110', '111'])).
% 4.84/5.09  thf('113', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_A) = (k1_xboole_0))
% 4.84/5.09          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('simplify', [status(thm)], ['112'])).
% 4.84/5.09  thf('114', plain, (((sk_A) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('115', plain, (((sk_B_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('116', plain, (((sk_C_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('117', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('simplify_reflect-', [status(thm)],
% 4.84/5.09                ['113', '114', '115', '116'])).
% 4.84/5.09  thf('118', plain,
% 4.84/5.09      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 4.84/5.09      inference('demod', [status(thm)], ['25', '30', '32'])).
% 4.84/5.09  thf('119', plain,
% 4.84/5.09      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.84/5.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.84/5.09  thf('120', plain,
% 4.84/5.09      (![X47 : $i, X48 : $i, X49 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ X47) @ X49)
% 4.84/5.09          | ~ (r2_hidden @ X47 @ (k2_zfmisc_1 @ X48 @ X49)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.84/5.09  thf('121', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['119', '120'])).
% 4.84/5.09  thf('122', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)) @ X0)
% 4.84/5.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 4.84/5.09      inference('sup+', [status(thm)], ['118', '121'])).
% 4.84/5.09  thf('123', plain,
% 4.84/5.09      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 4.84/5.09      inference('demod', [status(thm)], ['25', '30', '32'])).
% 4.84/5.09  thf('124', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)) @ X0)
% 4.84/5.09          | (v1_xboole_0 @ k1_xboole_0))),
% 4.84/5.09      inference('demod', [status(thm)], ['122', '123'])).
% 4.84/5.09  thf(t1_subset, axiom,
% 4.84/5.09    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 4.84/5.09  thf('125', plain,
% 4.84/5.09      (![X27 : $i, X28 : $i]:
% 4.84/5.09         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 4.84/5.09      inference('cnf', [status(esa)], [t1_subset])).
% 4.84/5.09  thf('126', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((v1_xboole_0 @ k1_xboole_0)
% 4.84/5.09          | (m1_subset_1 @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)) @ X0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['124', '125'])).
% 4.84/5.09  thf(t3_subset, axiom,
% 4.84/5.09    (![A:$i,B:$i]:
% 4.84/5.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.84/5.09  thf('127', plain,
% 4.84/5.09      (![X31 : $i, X32 : $i]:
% 4.84/5.09         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t3_subset])).
% 4.84/5.09  thf('128', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((v1_xboole_0 @ k1_xboole_0)
% 4.84/5.09          | (r1_tarski @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)) @ X0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['126', '127'])).
% 4.84/5.09  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.84/5.09  thf('129', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 4.84/5.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.84/5.09  thf(d10_xboole_0, axiom,
% 4.84/5.09    (![A:$i,B:$i]:
% 4.84/5.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.84/5.09  thf('130', plain,
% 4.84/5.09      (![X11 : $i, X13 : $i]:
% 4.84/5.09         (((X11) = (X13))
% 4.84/5.09          | ~ (r1_tarski @ X13 @ X11)
% 4.84/5.09          | ~ (r1_tarski @ X11 @ X13))),
% 4.84/5.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.84/5.09  thf('131', plain,
% 4.84/5.09      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['129', '130'])).
% 4.84/5.09  thf('132', plain,
% 4.84/5.09      (((v1_xboole_0 @ k1_xboole_0)
% 4.84/5.09        | ((k2_mcart_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['128', '131'])).
% 4.84/5.09  thf('133', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)) @ X0)
% 4.84/5.09          | (v1_xboole_0 @ k1_xboole_0))),
% 4.84/5.09      inference('demod', [status(thm)], ['122', '123'])).
% 4.84/5.09  thf('134', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((r2_hidden @ k1_xboole_0 @ X0)
% 4.84/5.09          | (v1_xboole_0 @ k1_xboole_0)
% 4.84/5.09          | (v1_xboole_0 @ k1_xboole_0))),
% 4.84/5.09      inference('sup+', [status(thm)], ['132', '133'])).
% 4.84/5.09  thf('135', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ k1_xboole_0 @ X0))),
% 4.84/5.09      inference('simplify', [status(thm)], ['134'])).
% 4.84/5.09  thf('136', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)) @ X0)
% 4.84/5.09          | (v1_xboole_0 @ k1_xboole_0))),
% 4.84/5.09      inference('demod', [status(thm)], ['122', '123'])).
% 4.84/5.09  thf('137', plain,
% 4.84/5.09      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.84/5.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.84/5.09  thf('138', plain,
% 4.84/5.09      (![X59 : $i, X60 : $i, X61 : $i]:
% 4.84/5.09         ((k4_zfmisc_1 @ X59 @ X60 @ X61 @ k1_xboole_0) = (k1_xboole_0))),
% 4.84/5.09      inference('simplify', [status(thm)], ['18'])).
% 4.84/5.09  thf('139', plain,
% 4.84/5.09      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.09         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.09           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.09      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.09  thf('140', plain,
% 4.84/5.09      (![X47 : $i, X48 : $i, X49 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ X47) @ X49)
% 4.84/5.09          | ~ (r2_hidden @ X47 @ (k2_zfmisc_1 @ X48 @ X49)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.84/5.09  thf('141', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.84/5.09         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['139', '140'])).
% 4.84/5.09  thf('142', plain,
% 4.84/5.09      (![X3 : $i]:
% 4.84/5.09         (~ (r2_hidden @ X3 @ k1_xboole_0)
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ X3) @ k1_xboole_0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['138', '141'])).
% 4.84/5.09  thf('143', plain,
% 4.84/5.09      (((v1_xboole_0 @ k1_xboole_0)
% 4.84/5.09        | (r2_hidden @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)) @ k1_xboole_0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['137', '142'])).
% 4.84/5.09  thf(t3_ordinal1, axiom,
% 4.84/5.09    (![A:$i,B:$i,C:$i]:
% 4.84/5.09     ( ~( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) & ( r2_hidden @ C @ A ) ) ))).
% 4.84/5.09  thf('144', plain,
% 4.84/5.09      (![X34 : $i, X35 : $i, X36 : $i]:
% 4.84/5.09         (~ (r2_hidden @ X34 @ X35)
% 4.84/5.09          | ~ (r2_hidden @ X36 @ X34)
% 4.84/5.09          | ~ (r2_hidden @ X35 @ X36))),
% 4.84/5.09      inference('cnf', [status(esa)], [t3_ordinal1])).
% 4.84/5.09  thf('145', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((v1_xboole_0 @ k1_xboole_0)
% 4.84/5.09          | ~ (r2_hidden @ k1_xboole_0 @ X0)
% 4.84/5.09          | ~ (r2_hidden @ X0 @ (k2_mcart_1 @ (sk_B @ k1_xboole_0))))),
% 4.84/5.09      inference('sup-', [status(thm)], ['143', '144'])).
% 4.84/5.09  thf('146', plain,
% 4.84/5.09      (((v1_xboole_0 @ k1_xboole_0)
% 4.84/5.09        | ~ (r2_hidden @ k1_xboole_0 @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)))
% 4.84/5.09        | (v1_xboole_0 @ k1_xboole_0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['136', '145'])).
% 4.84/5.09  thf('147', plain,
% 4.84/5.09      ((~ (r2_hidden @ k1_xboole_0 @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)))
% 4.84/5.09        | (v1_xboole_0 @ k1_xboole_0))),
% 4.84/5.09      inference('simplify', [status(thm)], ['146'])).
% 4.84/5.09  thf('148', plain,
% 4.84/5.09      (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ k1_xboole_0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['135', '147'])).
% 4.84/5.09  thf('149', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.84/5.09      inference('simplify', [status(thm)], ['148'])).
% 4.84/5.09  thf('150', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((v1_xboole_0 @ X0)
% 4.84/5.09          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('sup+', [status(thm)], ['117', '149'])).
% 4.84/5.09  thf(fc1_subset_1, axiom,
% 4.84/5.09    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.84/5.09  thf('151', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 4.84/5.09      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.84/5.09  thf('152', plain,
% 4.84/5.09      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09         (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))),
% 4.84/5.09      inference('sup-', [status(thm)], ['150', '151'])).
% 4.84/5.09  thf(d3_mcart_1, axiom,
% 4.84/5.09    (![A:$i,B:$i,C:$i]:
% 4.84/5.09     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 4.84/5.09  thf('153', plain,
% 4.84/5.09      (![X37 : $i, X38 : $i, X39 : $i]:
% 4.84/5.09         ((k3_mcart_1 @ X37 @ X38 @ X39)
% 4.84/5.09           = (k4_tarski @ (k4_tarski @ X37 @ X38) @ X39))),
% 4.84/5.09      inference('cnf', [status(esa)], [d3_mcart_1])).
% 4.84/5.09  thf('154', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 4.84/5.09           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 4.84/5.09           = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))),
% 4.84/5.09      inference('sup+', [status(thm)], ['152', '153'])).
% 4.84/5.09  thf('155', plain,
% 4.84/5.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.09        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['56', '59'])).
% 4.84/5.09  thf('156', plain,
% 4.84/5.09      (![X47 : $i, X48 : $i, X49 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ X47) @ X49)
% 4.84/5.09          | ~ (r2_hidden @ X47 @ (k2_zfmisc_1 @ X48 @ X49)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.84/5.09  thf('157', plain,
% 4.84/5.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.09        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 4.84/5.09      inference('sup-', [status(thm)], ['155', '156'])).
% 4.84/5.09  thf('158', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.84/5.09      inference('demod', [status(thm)], ['15', '16'])).
% 4.84/5.09  thf('159', plain,
% 4.84/5.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['7', '8'])).
% 4.84/5.09  thf('160', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         (((X1) = (k4_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 4.84/5.09      inference('sup+', [status(thm)], ['158', '159'])).
% 4.84/5.09  thf('161', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 4.84/5.09          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k4_xboole_0 @ X0 @ X0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['157', '160'])).
% 4.84/5.09  thf('162', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         ((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 4.84/5.09      inference('sup+', [status(thm)], ['17', '33'])).
% 4.84/5.09  thf('163', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0)
% 4.84/5.09            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) @ X0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 4.84/5.09      inference('sup+', [status(thm)], ['161', '162'])).
% 4.84/5.09  thf('164', plain,
% 4.84/5.09      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.09         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.09           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.09      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.09  thf('165', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 4.84/5.09      inference('demod', [status(thm)], ['163', '164'])).
% 4.84/5.09  thf('166', plain,
% 4.84/5.09      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 4.84/5.09         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 4.84/5.09          | ((X62) = (k1_xboole_0))
% 4.84/5.09          | ((X61) = (k1_xboole_0))
% 4.84/5.09          | ((X60) = (k1_xboole_0))
% 4.84/5.09          | ((X59) = (k1_xboole_0)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.09  thf('167', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0) != (k1_xboole_0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 4.84/5.09          | ((sk_A) = (k1_xboole_0))
% 4.84/5.09          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.09          | ((X0) = (k1_xboole_0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['165', '166'])).
% 4.84/5.09  thf('168', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_A) = (k1_xboole_0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 4.84/5.09      inference('simplify', [status(thm)], ['167'])).
% 4.84/5.09  thf('169', plain, (((sk_A) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('170', plain, (((sk_B_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('171', plain, (((sk_C_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('172', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 4.84/5.09      inference('simplify_reflect-', [status(thm)],
% 4.84/5.09                ['168', '169', '170', '171'])).
% 4.84/5.09  thf('173', plain,
% 4.84/5.09      (![X27 : $i, X28 : $i]:
% 4.84/5.09         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 4.84/5.09      inference('cnf', [status(esa)], [t1_subset])).
% 4.84/5.09  thf('174', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 4.84/5.09      inference('sup-', [status(thm)], ['172', '173'])).
% 4.84/5.09  thf('175', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.84/5.09      inference('simplify', [status(thm)], ['148'])).
% 4.84/5.09  thf('176', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((v1_xboole_0 @ X0)
% 4.84/5.09          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 4.84/5.09      inference('sup+', [status(thm)], ['174', '175'])).
% 4.84/5.09  thf('177', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 4.84/5.09      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.84/5.09  thf('178', plain,
% 4.84/5.09      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)),
% 4.84/5.09      inference('sup-', [status(thm)], ['176', '177'])).
% 4.84/5.09  thf('179', plain,
% 4.84/5.09      (![X67 : $i, X68 : $i, X69 : $i]:
% 4.84/5.09         (~ (m1_subset_1 @ X67 @ sk_B_2)
% 4.84/5.09          | ((sk_E_1) != (k3_mcart_1 @ X68 @ X67 @ X69))
% 4.84/5.09          | ((sk_D_1) = (X69))
% 4.84/5.09          | ~ (m1_subset_1 @ X69 @ sk_C_2)
% 4.84/5.09          | ~ (m1_subset_1 @ X68 @ sk_A))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('180', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         (~ (m1_subset_1 @ X0 @ sk_A)
% 4.84/5.09          | ~ (m1_subset_1 @ X1 @ sk_C_2)
% 4.84/5.09          | ((sk_D_1) = (X1))
% 4.84/5.09          | ((sk_E_1)
% 4.84/5.09              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X1)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['178', '179'])).
% 4.84/5.09  thf('181', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 4.84/5.09          | ((sk_D_1) = (X0))
% 4.84/5.09          | ~ (m1_subset_1 @ X0 @ sk_C_2)
% 4.84/5.09          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 4.84/5.09      inference('sup-', [status(thm)], ['154', '180'])).
% 4.84/5.09  thf('182', plain,
% 4.84/5.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.09        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['56', '59'])).
% 4.84/5.09  thf('183', plain,
% 4.84/5.09      (![X47 : $i, X48 : $i, X49 : $i]:
% 4.84/5.09         ((r2_hidden @ (k1_mcart_1 @ X47) @ X48)
% 4.84/5.09          | ~ (r2_hidden @ X47 @ (k2_zfmisc_1 @ X48 @ X49)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.84/5.09  thf('184', plain,
% 4.84/5.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.09        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 4.84/5.09      inference('sup-', [status(thm)], ['182', '183'])).
% 4.84/5.09  thf('185', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         (((X1) = (k4_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 4.84/5.09      inference('sup+', [status(thm)], ['158', '159'])).
% 4.84/5.09  thf('186', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 4.84/5.09          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k4_xboole_0 @ X0 @ X0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['184', '185'])).
% 4.84/5.09  thf('187', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         ((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 4.84/5.09      inference('sup+', [status(thm)], ['17', '33'])).
% 4.84/5.09  thf('188', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0)
% 4.84/5.09            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) @ X0))
% 4.84/5.09          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 4.84/5.09      inference('sup+', [status(thm)], ['186', '187'])).
% 4.84/5.09  thf('189', plain,
% 4.84/5.09      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.09         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.09           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.09      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.09  thf('190', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0))
% 4.84/5.09          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 4.84/5.09      inference('demod', [status(thm)], ['188', '189'])).
% 4.84/5.09  thf('191', plain,
% 4.84/5.09      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 4.84/5.09         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 4.84/5.09          | ((X62) = (k1_xboole_0))
% 4.84/5.09          | ((X61) = (k1_xboole_0))
% 4.84/5.09          | ((X60) = (k1_xboole_0))
% 4.84/5.09          | ((X59) = (k1_xboole_0)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.09  thf('192', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0) != (k1_xboole_0))
% 4.84/5.09          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 4.84/5.09          | ((sk_A) = (k1_xboole_0))
% 4.84/5.09          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.09          | ((X0) = (k1_xboole_0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['190', '191'])).
% 4.84/5.09  thf('193', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_A) = (k1_xboole_0))
% 4.84/5.09          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 4.84/5.09      inference('simplify', [status(thm)], ['192'])).
% 4.84/5.09  thf('194', plain, (((sk_A) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('195', plain, (((sk_B_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('196', plain, (((sk_C_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('197', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 4.84/5.09      inference('simplify_reflect-', [status(thm)],
% 4.84/5.09                ['193', '194', '195', '196'])).
% 4.84/5.09  thf('198', plain,
% 4.84/5.09      (![X27 : $i, X28 : $i]:
% 4.84/5.09         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 4.84/5.09      inference('cnf', [status(esa)], [t1_subset])).
% 4.84/5.09  thf('199', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 4.84/5.09      inference('sup-', [status(thm)], ['197', '198'])).
% 4.84/5.09  thf('200', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 4.84/5.09      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.84/5.09  thf('201', plain,
% 4.84/5.09      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.84/5.09        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 4.84/5.09      inference('sup-', [status(thm)], ['199', '200'])).
% 4.84/5.09  thf('202', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.84/5.09      inference('simplify', [status(thm)], ['148'])).
% 4.84/5.09  thf('203', plain,
% 4.84/5.09      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)),
% 4.84/5.09      inference('demod', [status(thm)], ['201', '202'])).
% 4.84/5.09  thf('204', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 4.84/5.09          | ((sk_D_1) = (X0))
% 4.84/5.09          | ~ (m1_subset_1 @ X0 @ sk_C_2))),
% 4.84/5.09      inference('demod', [status(thm)], ['181', '203'])).
% 4.84/5.09  thf('205', plain,
% 4.84/5.09      ((((sk_E_1) != (sk_E_1))
% 4.84/5.09        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_2)
% 4.84/5.09        | ((sk_D_1) = (k2_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['55', '204'])).
% 4.84/5.09  thf('206', plain,
% 4.84/5.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.09        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['0', '1'])).
% 4.84/5.09  thf('207', plain,
% 4.84/5.09      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.84/5.09         ((k3_zfmisc_1 @ X40 @ X41 @ X42)
% 4.84/5.09           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41) @ X42))),
% 4.84/5.09      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.84/5.09  thf('208', plain,
% 4.84/5.09      (![X47 : $i, X48 : $i, X49 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ X47) @ X49)
% 4.84/5.09          | ~ (r2_hidden @ X47 @ (k2_zfmisc_1 @ X48 @ X49)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.84/5.09  thf('209', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.84/5.09         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 4.84/5.09      inference('sup-', [status(thm)], ['207', '208'])).
% 4.84/5.09  thf('210', plain,
% 4.84/5.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))
% 4.84/5.09        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_2))),
% 4.84/5.09      inference('sup-', [status(thm)], ['206', '209'])).
% 4.84/5.09  thf('211', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         (((X1) = (k4_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 4.84/5.09      inference('sup+', [status(thm)], ['158', '159'])).
% 4.84/5.09  thf('212', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_2)
% 4.84/5.09          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k4_xboole_0 @ X0 @ X0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['210', '211'])).
% 4.84/5.09  thf('213', plain,
% 4.84/5.09      (![X0 : $i, X1 : $i]:
% 4.84/5.09         ((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 4.84/5.09      inference('sup+', [status(thm)], ['17', '33'])).
% 4.84/5.09  thf('214', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0)
% 4.84/5.09            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2) @ X0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_2))),
% 4.84/5.09      inference('sup+', [status(thm)], ['212', '213'])).
% 4.84/5.09  thf('215', plain,
% 4.84/5.09      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.84/5.09         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46)
% 4.84/5.09           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X43 @ X44 @ X45) @ X46))),
% 4.84/5.09      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 4.84/5.09  thf('216', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2 @ X0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_2))),
% 4.84/5.09      inference('demod', [status(thm)], ['214', '215'])).
% 4.84/5.09  thf('217', plain,
% 4.84/5.09      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 4.84/5.09         (((k4_zfmisc_1 @ X59 @ X60 @ X61 @ X62) != (k1_xboole_0))
% 4.84/5.09          | ((X62) = (k1_xboole_0))
% 4.84/5.09          | ((X61) = (k1_xboole_0))
% 4.84/5.09          | ((X60) = (k1_xboole_0))
% 4.84/5.09          | ((X59) = (k1_xboole_0)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t55_mcart_1])).
% 4.84/5.09  thf('218', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((k1_xboole_0) != (k1_xboole_0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_2)
% 4.84/5.09          | ((sk_A) = (k1_xboole_0))
% 4.84/5.09          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.09          | ((X0) = (k1_xboole_0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['216', '217'])).
% 4.84/5.09  thf('219', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | ((sk_C_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09          | ((sk_A) = (k1_xboole_0))
% 4.84/5.09          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_2))),
% 4.84/5.09      inference('simplify', [status(thm)], ['218'])).
% 4.84/5.09  thf('220', plain, (((sk_A) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('221', plain, (((sk_B_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('222', plain, (((sk_C_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('223', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0)) | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_2))),
% 4.84/5.09      inference('simplify_reflect-', [status(thm)],
% 4.84/5.09                ['219', '220', '221', '222'])).
% 4.84/5.09  thf('224', plain,
% 4.84/5.09      (![X27 : $i, X28 : $i]:
% 4.84/5.09         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 4.84/5.09      inference('cnf', [status(esa)], [t1_subset])).
% 4.84/5.09  thf('225', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         (((X0) = (k1_xboole_0))
% 4.84/5.09          | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_2))),
% 4.84/5.09      inference('sup-', [status(thm)], ['223', '224'])).
% 4.84/5.09  thf('226', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.84/5.09      inference('simplify', [status(thm)], ['148'])).
% 4.84/5.09  thf('227', plain,
% 4.84/5.09      (![X0 : $i]:
% 4.84/5.09         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_2))),
% 4.84/5.09      inference('sup+', [status(thm)], ['225', '226'])).
% 4.84/5.09  thf('228', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 4.84/5.09      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.84/5.09  thf('229', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_2)),
% 4.84/5.09      inference('sup-', [status(thm)], ['227', '228'])).
% 4.84/5.09  thf('230', plain,
% 4.84/5.09      ((((sk_E_1) != (sk_E_1)) | ((sk_D_1) = (k2_mcart_1 @ sk_E_1)))),
% 4.84/5.09      inference('demod', [status(thm)], ['205', '229'])).
% 4.84/5.09  thf('231', plain, (((sk_D_1) = (k2_mcart_1 @ sk_E_1))),
% 4.84/5.09      inference('simplify', [status(thm)], ['230'])).
% 4.84/5.09  thf('232', plain,
% 4.84/5.09      (((sk_D_1) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_E_1))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('233', plain,
% 4.84/5.09      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_2))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf(t50_mcart_1, axiom,
% 4.84/5.09    (![A:$i,B:$i,C:$i]:
% 4.84/5.09     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 4.84/5.09          ( ( C ) != ( k1_xboole_0 ) ) & 
% 4.84/5.09          ( ~( ![D:$i]:
% 4.84/5.09               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 4.84/5.09                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 4.84/5.09                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 4.84/5.09                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 4.84/5.09                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 4.84/5.09                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 4.84/5.09  thf('234', plain,
% 4.84/5.09      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 4.84/5.09         (((X55) = (k1_xboole_0))
% 4.84/5.09          | ((X56) = (k1_xboole_0))
% 4.84/5.09          | ((k7_mcart_1 @ X55 @ X56 @ X58 @ X57) = (k2_mcart_1 @ X57))
% 4.84/5.09          | ~ (m1_subset_1 @ X57 @ (k3_zfmisc_1 @ X55 @ X56 @ X58))
% 4.84/5.09          | ((X58) = (k1_xboole_0)))),
% 4.84/5.09      inference('cnf', [status(esa)], [t50_mcart_1])).
% 4.84/5.09  thf('235', plain,
% 4.84/5.09      ((((sk_C_2) = (k1_xboole_0))
% 4.84/5.09        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_E_1)
% 4.84/5.09            = (k2_mcart_1 @ sk_E_1))
% 4.84/5.09        | ((sk_B_2) = (k1_xboole_0))
% 4.84/5.09        | ((sk_A) = (k1_xboole_0)))),
% 4.84/5.09      inference('sup-', [status(thm)], ['233', '234'])).
% 4.84/5.09  thf('236', plain, (((sk_A) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('237', plain, (((sk_B_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('238', plain, (((sk_C_2) != (k1_xboole_0))),
% 4.84/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.84/5.09  thf('239', plain,
% 4.84/5.09      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 4.84/5.09      inference('simplify_reflect-', [status(thm)],
% 4.84/5.09                ['235', '236', '237', '238'])).
% 4.84/5.09  thf('240', plain, (((sk_D_1) != (k2_mcart_1 @ sk_E_1))),
% 4.84/5.09      inference('demod', [status(thm)], ['232', '239'])).
% 4.84/5.09  thf('241', plain, ($false),
% 4.84/5.09      inference('simplify_reflect-', [status(thm)], ['231', '240'])).
% 4.84/5.09  
% 4.84/5.09  % SZS output end Refutation
% 4.84/5.09  
% 4.84/5.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
