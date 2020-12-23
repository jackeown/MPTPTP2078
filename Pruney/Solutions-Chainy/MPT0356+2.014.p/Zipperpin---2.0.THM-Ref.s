%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iGyo2svam4

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:19 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 224 expanded)
%              Number of leaves         :   37 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  765 (1607 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_subset_1 @ X40 @ X41 )
        = ( k4_xboole_0 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_subset_1 @ X40 @ X41 )
        = ( k4_xboole_0 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X36: $i] :
      ( r1_tarski @ ( k1_tarski @ X36 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X27: $i] :
      ( ( k2_enumset1 @ X27 @ X27 @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k2_tarski @ X32 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( m1_subset_1 @ X37 @ X38 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X42: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_subset_1 @ X40 @ X41 )
        = ( k4_xboole_0 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','29'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X44 @ X43 ) @ ( k3_subset_1 @ X44 @ X45 ) )
      | ( r1_tarski @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    | ( r1_tarski @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    | ( r1_tarski @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k5_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('60',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['37','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('65',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('69',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('71',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['66','73'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['4','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iGyo2svam4
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.64  % Solved by: fo/fo7.sh
% 0.44/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.64  % done 468 iterations in 0.186s
% 0.44/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.64  % SZS output start Refutation
% 0.44/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.64  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.44/0.64  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.44/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.64  thf(t35_subset_1, conjecture,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64       ( ![C:$i]:
% 0.44/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.44/0.64             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.64    (~( ![A:$i,B:$i]:
% 0.44/0.64        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64          ( ![C:$i]:
% 0.44/0.64            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.44/0.64                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.44/0.64    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 0.44/0.64  thf('0', plain, (~ (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(d5_subset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.44/0.64  thf('2', plain,
% 0.44/0.64      (![X40 : $i, X41 : $i]:
% 0.44/0.64         (((k3_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))
% 0.44/0.64          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40)))),
% 0.44/0.64      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.64  thf('3', plain,
% 0.44/0.64      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.64  thf('4', plain, (~ (r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.64  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('6', plain,
% 0.44/0.64      (![X40 : $i, X41 : $i]:
% 0.44/0.64         (((k3_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))
% 0.44/0.64          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40)))),
% 0.44/0.64      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.64  thf('7', plain,
% 0.44/0.64      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.65  thf(t80_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      (![X36 : $i]: (r1_tarski @ (k1_tarski @ X36) @ (k1_zfmisc_1 @ X36))),
% 0.44/0.65      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.44/0.65  thf(t77_enumset1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      (![X25 : $i, X26 : $i]:
% 0.44/0.65         ((k2_enumset1 @ X25 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.44/0.65      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.44/0.65  thf(t82_enumset1, axiom,
% 0.44/0.65    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X27 : $i]: ((k2_enumset1 @ X27 @ X27 @ X27 @ X27) = (k1_tarski @ X27))),
% 0.44/0.65      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.44/0.65  thf('11', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['9', '10'])).
% 0.44/0.65  thf(t38_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.44/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.44/0.65         ((r2_hidden @ X32 @ X33)
% 0.44/0.65          | ~ (r1_tarski @ (k2_tarski @ X32 @ X34) @ X33))),
% 0.44/0.65      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.65  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['8', '13'])).
% 0.44/0.65  thf(d2_subset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.44/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.44/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      (![X37 : $i, X38 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X37 @ X38)
% 0.44/0.65          | (m1_subset_1 @ X37 @ X38)
% 0.44/0.65          | (v1_xboole_0 @ X38))),
% 0.44/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.65  thf(fc1_subset_1, axiom,
% 0.44/0.65    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.44/0.65  thf('17', plain, (![X42 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X42))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.44/0.65  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.65      inference('clc', [status(thm)], ['16', '17'])).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X40 : $i, X41 : $i]:
% 0.44/0.65         (((k3_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))
% 0.44/0.65          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.44/0.65  thf('21', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.44/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.65  thf(t7_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.65  thf('22', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.65  thf(t73_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.44/0.65       ( r1_tarski @ A @ B ) ))).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.65         ((r1_tarski @ X14 @ X15)
% 0.44/0.65          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.44/0.65          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.44/0.65      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X1 @ X0) | (r1_tarski @ X1 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.65  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '24'])).
% 0.44/0.65  thf(t12_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      (![X5 : $i, X6 : $i]:
% 0.44/0.65         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.44/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.65  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.65  thf(d6_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( k5_xboole_0 @ A @ B ) =
% 0.44/0.65       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((k5_xboole_0 @ X0 @ X1)
% 0.44/0.65           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.44/0.65  thf('29', plain,
% 0.44/0.65      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['27', '28'])).
% 0.44/0.65  thf('30', plain,
% 0.44/0.65      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['20', '29'])).
% 0.44/0.65  thf(t31_subset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.65       ( ![C:$i]:
% 0.44/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.65           ( ( r1_tarski @ B @ C ) <=>
% 0.44/0.65             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.65  thf('31', plain,
% 0.44/0.65      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.44/0.65          | ~ (r1_tarski @ (k3_subset_1 @ X44 @ X43) @ 
% 0.44/0.65               (k3_subset_1 @ X44 @ X45))
% 0.44/0.65          | (r1_tarski @ X45 @ X43)
% 0.44/0.65          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 0.44/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (r1_tarski @ X1 @ X0)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.65  thf('33', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.65      inference('clc', [status(thm)], ['16', '17'])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 0.44/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (r1_tarski @ X1 @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ 
% 0.44/0.65           (k4_xboole_0 @ sk_A @ sk_C))
% 0.44/0.65        | (r1_tarski @ sk_C @ sk_A)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['7', '34'])).
% 0.44/0.65  thf('36', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('37', plain,
% 0.44/0.65      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ 
% 0.44/0.65           (k4_xboole_0 @ sk_A @ sk_C))
% 0.44/0.65        | (r1_tarski @ sk_C @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.65  thf('38', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '24'])).
% 0.44/0.65  thf('39', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '24'])).
% 0.44/0.65  thf(t110_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.44/0.65       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.44/0.65  thf('40', plain,
% 0.44/0.65      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.65         (~ (r1_tarski @ X2 @ X3)
% 0.44/0.65          | ~ (r1_tarski @ X4 @ X3)
% 0.44/0.65          | (r1_tarski @ (k5_xboole_0 @ X2 @ X4) @ X3))),
% 0.44/0.65      inference('cnf', [status(esa)], [t110_xboole_1])).
% 0.44/0.65  thf('41', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.65  thf('42', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['38', '41'])).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (![X5 : $i, X6 : $i]:
% 0.44/0.65         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.44/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.65  thf('44', plain,
% 0.44/0.65      (![X0 : $i]: ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['27', '28'])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.65  thf(t85_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.44/0.65  thf('47', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.65         (~ (r1_tarski @ X19 @ X20)
% 0.44/0.65          | (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.44/0.65  thf('48', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.44/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.65  thf('49', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.44/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.65  thf('50', plain,
% 0.44/0.65      (![X5 : $i, X6 : $i]:
% 0.44/0.65         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.44/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.65  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.65  thf('52', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.65         ((r1_tarski @ X14 @ X15)
% 0.44/0.65          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.44/0.65          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.44/0.65      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.44/0.65  thf('53', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_tarski @ X1 @ X0)
% 0.44/0.65          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.44/0.65          | (r1_tarski @ X1 @ k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.65  thf('54', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r1_tarski @ X1 @ k1_xboole_0)
% 0.44/0.65          | ~ (r1_tarski @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['48', '53'])).
% 0.44/0.65  thf('55', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r1_tarski @ X1 @ 
% 0.44/0.65             (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))
% 0.44/0.65          | (r1_tarski @ X1 @ k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['45', '54'])).
% 0.44/0.65  thf('56', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ 
% 0.44/0.65             (k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)))
% 0.44/0.65          | (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['44', '55'])).
% 0.44/0.65  thf('57', plain,
% 0.44/0.65      (![X0 : $i]: ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.65  thf('58', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '24'])).
% 0.44/0.65  thf('59', plain,
% 0.44/0.65      (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ k1_xboole_0)),
% 0.44/0.65      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.44/0.65  thf(t3_xboole_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.65  thf('60', plain,
% 0.44/0.65      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.44/0.65  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.44/0.65  thf('62', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.44/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.65  thf('63', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.44/0.65      inference('demod', [status(thm)], ['37', '61', '62'])).
% 0.44/0.65  thf('64', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '24'])).
% 0.44/0.65  thf('65', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.65         (~ (r1_tarski @ X19 @ X20)
% 0.44/0.65          | (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.44/0.65  thf('66', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.44/0.65  thf('67', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('68', plain,
% 0.44/0.65      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.65  thf('69', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.65  thf('70', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '24'])).
% 0.44/0.65  thf(t64_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.44/0.65         ( r1_xboole_0 @ B @ D ) ) =>
% 0.44/0.65       ( r1_xboole_0 @ A @ C ) ))).
% 0.44/0.65  thf('71', plain,
% 0.44/0.65      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X9 @ X10)
% 0.44/0.65          | ~ (r1_tarski @ X9 @ X11)
% 0.44/0.65          | ~ (r1_tarski @ X10 @ X12)
% 0.44/0.65          | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.44/0.65  thf('72', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ X1)
% 0.44/0.65          | ~ (r1_tarski @ X2 @ X1)
% 0.44/0.65          | (r1_xboole_0 @ X0 @ X2))),
% 0.44/0.65      inference('sup-', [status(thm)], ['70', '71'])).
% 0.44/0.65  thf('73', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X0 @ sk_B)
% 0.44/0.65          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['69', '72'])).
% 0.44/0.65  thf('74', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.44/0.65      inference('sup-', [status(thm)], ['66', '73'])).
% 0.44/0.65  thf(t86_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.44/0.65       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.44/0.65  thf('75', plain,
% 0.44/0.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.65         (~ (r1_tarski @ X22 @ X23)
% 0.44/0.65          | ~ (r1_xboole_0 @ X22 @ X24)
% 0.44/0.65          | (r1_tarski @ X22 @ (k4_xboole_0 @ X23 @ X24)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.44/0.65  thf('76', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r1_tarski @ sk_C @ (k4_xboole_0 @ X0 @ sk_B))
% 0.44/0.65          | ~ (r1_tarski @ sk_C @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.44/0.65  thf('77', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['63', '76'])).
% 0.44/0.65  thf('78', plain, ($false), inference('demod', [status(thm)], ['4', '77'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
