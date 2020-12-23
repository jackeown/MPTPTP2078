%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7LTjlEXwZW

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  166 (7895 expanded)
%              Number of leaves         :   26 (2208 expanded)
%              Depth                    :   43
%              Number of atoms          : 1483 (83981 expanded)
%              Number of equality atoms :  249 (13714 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_C_1 @ sk_D_1 )
      = ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X30
        = ( k2_tarski @ X28 @ X29 ) )
      | ( X30
        = ( k1_tarski @ X29 ) )
      | ( X30
        = ( k1_tarski @ X28 ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k2_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('7',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X19 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('9',plain,(
    ! [X16: $i,X19: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X19 @ X16 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X18 )
      | ( X20 = X19 )
      | ( X20 = X16 )
      | ( X18
       != ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X16: $i,X19: $i,X20: $i] :
      ( ( X20 = X16 )
      | ( X20 = X19 )
      | ~ ( r2_hidden @ X20 @ ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_C_1 = sk_B )
    | ( sk_C_1 = sk_A ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_C_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X16: $i,X19: $i] :
      ( r2_hidden @ X16 @ ( k2_tarski @ X19 @ X16 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    | ( sk_C_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( sk_C_1 = sk_B )
    | ( sk_B = sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_C_1 ) )
    | ( sk_B = sk_D_1 )
    | ( sk_C_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('29',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C_1 = sk_B )
    | ( sk_B = sk_D_1 )
    | ( sk_B = sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = sk_D_1 )
    | ( sk_C_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_C_1 = sk_B )
    | ( sk_B = sk_D_1 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = sk_D_1 )
    | ( sk_C_1 = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( sk_B = sk_D_1 )
    | ( sk_C_1 = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf(t18_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X34 ) )
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t18_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != ( k1_tarski @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ( sk_B = sk_D_1 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ( sk_B = sk_D_1 )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C_1 = sk_B )
      | ( sk_B = sk_D_1 )
      | ( sk_A = X0 )
      | ( sk_B = sk_D_1 )
      | ( sk_C_1 = sk_B ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( sk_B = sk_D_1 )
      | ( sk_C_1 = sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( sk_B = sk_D_1 )
      | ( sk_C_1 = sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( sk_C_1 = sk_B )
      | ( sk_B = sk_D_1 )
      | ( sk_C_1 = sk_B )
      | ( sk_B = sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = sk_D_1 )
      | ( sk_C_1 = sk_B )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_B = sk_D_1 )
    | ( sk_C_1 = sk_B ) ),
    inference(condensation,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_C_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('57',plain,(
    ! [X16: $i,X19: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X19 @ X16 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    | ( sk_C_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('61',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( sk_C_1 = sk_B )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( sk_C_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_C_1 ) )
    | ( sk_C_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('67',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C_1 = sk_B ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('69',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( sk_C_1 = sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
    | ( sk_C_1 = sk_B )
    | ( sk_C_1 = sk_B ) ),
    inference('sup+',[status(thm)],['54','69'])).

thf('71',plain,
    ( ( sk_C_1 = sk_B )
    | ( r2_hidden @ sk_D_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C_1 = sk_B ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('74',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_C_1 = sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('76',plain,
    ( ( sk_C_1 = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_C_1 = sk_B )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_C_1 = sk_B )
    | ( sk_D_1 = sk_A )
    | ( sk_C_1 = sk_B ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,
    ( ( sk_D_1 = sk_A )
    | ( sk_C_1 = sk_B ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_C_1 = sk_B ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_C_1 = sk_B ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('84',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) @ ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 ) )
    | ( ( k2_tarski @ sk_C_1 @ sk_D_1 )
      = ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','82','83'])).

thf('85',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('86',plain,(
    ! [X16: $i,X19: $i] :
      ( r2_hidden @ X16 @ ( k2_tarski @ X19 @ X16 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('87',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('89',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B )
    | ( sk_D_1 = sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_C_1 = sk_B ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('93',plain,(
    sk_C_1 = sk_B ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('94',plain,(
    sk_C_1 = sk_B ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('95',plain,(
    sk_C_1 = sk_B ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('96',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_C_1 ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('98',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_C_1 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('100',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( sk_D_1 = sk_C_1 )
    | ( sk_C_1 = sk_D_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_D_1 = sk_C_1 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('103',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_C_1 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('105',plain,
    ( ( sk_D_1 = sk_C_1 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( sk_D_1 = sk_C_1 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('109',plain,
    ( ( r2_hidden @ sk_C_1 @ k1_xboole_0 )
    | ( sk_D_1 = sk_C_1 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_D_1 = sk_C_1 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('112',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_D_1 = sk_C_1 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('114',plain,
    ( ( sk_D_1 = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D_1 = sk_C_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_D_1 = sk_C_1 )
    | ( sk_C_1 = sk_A )
    | ( sk_D_1 = sk_C_1 ) ),
    inference('sup-',[status(thm)],['109','116'])).

thf('118',plain,
    ( ( sk_C_1 = sk_A )
    | ( sk_D_1 = sk_C_1 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    sk_D_1 = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf(t94_enumset1,axiom,(
    ! [A: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('121',plain,(
    ! [X27: $i] :
      ( ( k5_enumset1 @ X27 @ X27 @ X27 @ X27 @ X27 @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_enumset1])).

thf(t89_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('122',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X24 @ X24 @ X24 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t89_enumset1])).

thf('123',plain,(
    ! [X27: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('127',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ ( k2_tarski @ X28 @ X31 ) )
      | ( X30
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('128',plain,(
    ! [X28: $i,X31: $i] :
      ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X28 @ X31 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','128'])).

thf('130',plain,(
    sk_D_1 = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('132',plain,
    ( ( k1_tarski @ sk_C_1 )
    = ( k1_enumset1 @ sk_A @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['84','120','125','129','130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('134',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('136',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7LTjlEXwZW
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.46/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.71  % Solved by: fo/fo7.sh
% 0.46/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.71  % done 479 iterations in 0.247s
% 0.46/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.71  % SZS output start Refutation
% 0.46/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.71  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.71  thf(t28_zfmisc_1, conjecture,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.71          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.71             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.46/0.71    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.46/0.71  thf('0', plain,
% 0.46/0.71      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t70_enumset1, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.71  thf('1', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i]:
% 0.46/0.71         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.71  thf('2', plain,
% 0.46/0.71      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 0.46/0.71        (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.46/0.71      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.71  thf(d10_xboole_0, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.71  thf('3', plain,
% 0.46/0.71      (![X0 : $i, X2 : $i]:
% 0.46/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.71  thf('4', plain,
% 0.46/0.71      ((~ (r1_tarski @ (k2_tarski @ sk_C_1 @ sk_D_1) @ 
% 0.46/0.71           (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 0.46/0.71        | ((k2_tarski @ sk_C_1 @ sk_D_1) = (k1_enumset1 @ sk_A @ sk_A @ sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('5', plain,
% 0.46/0.71      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 0.46/0.71        (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.46/0.71      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.71  thf(l45_zfmisc_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.46/0.71       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.46/0.71            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.46/0.71  thf('6', plain,
% 0.46/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.71         (((X30) = (k2_tarski @ X28 @ X29))
% 0.46/0.71          | ((X30) = (k1_tarski @ X29))
% 0.46/0.71          | ((X30) = (k1_tarski @ X28))
% 0.46/0.71          | ((X30) = (k1_xboole_0))
% 0.46/0.71          | ~ (r1_tarski @ X30 @ (k2_tarski @ X28 @ X29)))),
% 0.46/0.71      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.46/0.71  thf('7', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.71  thf(d2_tarski, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.71       ( ![D:$i]:
% 0.46/0.71         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.46/0.71  thf('8', plain,
% 0.46/0.71      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.71         (((X17) != (X19))
% 0.46/0.71          | (r2_hidden @ X17 @ X18)
% 0.46/0.71          | ((X18) != (k2_tarski @ X19 @ X16)))),
% 0.46/0.71      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.71  thf('9', plain,
% 0.46/0.71      (![X16 : $i, X19 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X19 @ X16))),
% 0.46/0.71      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.71  thf('10', plain,
% 0.46/0.71      (((r2_hidden @ sk_C_1 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['7', '9'])).
% 0.46/0.71  thf('11', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i]:
% 0.46/0.71         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.71  thf('12', plain,
% 0.46/0.71      (![X16 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.71         (~ (r2_hidden @ X20 @ X18)
% 0.46/0.71          | ((X20) = (X19))
% 0.46/0.71          | ((X20) = (X16))
% 0.46/0.71          | ((X18) != (k2_tarski @ X19 @ X16)))),
% 0.46/0.71      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.71  thf('13', plain,
% 0.46/0.71      (![X16 : $i, X19 : $i, X20 : $i]:
% 0.46/0.71         (((X20) = (X16))
% 0.46/0.71          | ((X20) = (X19))
% 0.46/0.71          | ~ (r2_hidden @ X20 @ (k2_tarski @ X19 @ X16)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.71  thf('14', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.46/0.71          | ((X2) = (X1))
% 0.46/0.71          | ((X2) = (X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['11', '13'])).
% 0.46/0.71  thf('15', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((sk_C_1) = (sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['10', '14'])).
% 0.46/0.71  thf('16', plain, (((sk_A) != (sk_C_1))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('17', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.46/0.71  thf('18', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i]:
% 0.46/0.71         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.71  thf('19', plain,
% 0.46/0.71      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.71         (((X17) != (X16))
% 0.46/0.71          | (r2_hidden @ X17 @ X18)
% 0.46/0.71          | ((X18) != (k2_tarski @ X19 @ X16)))),
% 0.46/0.71      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.71  thf('20', plain,
% 0.46/0.71      (![X16 : $i, X19 : $i]: (r2_hidden @ X16 @ (k2_tarski @ X19 @ X16))),
% 0.46/0.71      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.71  thf('21', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['18', '20'])).
% 0.46/0.71  thf('22', plain,
% 0.46/0.71      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['17', '21'])).
% 0.46/0.71  thf(d1_tarski, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.71  thf('23', plain,
% 0.46/0.71      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.46/0.71         (~ (r2_hidden @ X14 @ X13)
% 0.46/0.71          | ((X14) = (X11))
% 0.46/0.71          | ((X13) != (k1_tarski @ X11)))),
% 0.46/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.71  thf('24', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('25', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((sk_B) = (sk_D_1)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['22', '24'])).
% 0.46/0.71  thf('26', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['18', '20'])).
% 0.46/0.71  thf('27', plain,
% 0.46/0.71      (((r2_hidden @ sk_B @ (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((sk_B) = (sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.71  thf('28', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('29', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((sk_B) = (sk_D_1))
% 0.46/0.71        | ((sk_B) = (sk_C_1)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.71  thf('30', plain,
% 0.46/0.71      ((((sk_B) = (sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.71  thf('31', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i]:
% 0.46/0.71         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.71  thf(t12_zfmisc_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.46/0.71  thf('32', plain,
% 0.46/0.71      (![X32 : $i, X33 : $i]:
% 0.46/0.71         (r1_tarski @ (k1_tarski @ X32) @ (k2_tarski @ X32 @ X33))),
% 0.46/0.71      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.46/0.71  thf('33', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.71  thf('34', plain,
% 0.46/0.71      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((sk_B) = (sk_D_1)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['30', '33'])).
% 0.46/0.71  thf(t4_boole, axiom,
% 0.46/0.71    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.71  thf('35', plain,
% 0.46/0.71      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [t4_boole])).
% 0.46/0.71  thf(l32_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.71  thf('36', plain,
% 0.46/0.71      (![X3 : $i, X4 : $i]:
% 0.46/0.71         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.46/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.71  thf('37', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.71  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.71      inference('simplify', [status(thm)], ['37'])).
% 0.46/0.71  thf('39', plain,
% 0.46/0.71      (![X0 : $i, X2 : $i]:
% 0.46/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.71  thf('40', plain,
% 0.46/0.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.71  thf('41', plain,
% 0.46/0.71      ((((sk_B) = (sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['34', '40'])).
% 0.46/0.71  thf('42', plain,
% 0.46/0.71      ((((sk_B) = (sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['34', '40'])).
% 0.46/0.71  thf(t18_zfmisc_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.71         ( k1_tarski @ A ) ) =>
% 0.46/0.71       ( ( A ) = ( B ) ) ))).
% 0.46/0.71  thf('43', plain,
% 0.46/0.71      (![X34 : $i, X35 : $i]:
% 0.46/0.71         (((X35) = (X34))
% 0.46/0.71          | ((k3_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X34))
% 0.46/0.71              != (k1_tarski @ X35)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t18_zfmisc_1])).
% 0.46/0.71  thf('44', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_tarski @ sk_A))
% 0.46/0.71          | ((sk_C_1) = (sk_B))
% 0.46/0.71          | ((sk_B) = (sk_D_1))
% 0.46/0.71          | ((sk_A) = (X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.71  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.71      inference('simplify', [status(thm)], ['37'])).
% 0.46/0.71  thf(t28_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.71  thf('46', plain,
% 0.46/0.71      (![X8 : $i, X9 : $i]:
% 0.46/0.71         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.46/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.71  thf('47', plain,
% 0.46/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.71  thf('48', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k1_xboole_0) != (k1_tarski @ sk_A))
% 0.46/0.71          | ((sk_C_1) = (sk_B))
% 0.46/0.71          | ((sk_B) = (sk_D_1))
% 0.46/0.71          | ((sk_A) = (X0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['44', '47'])).
% 0.46/0.71  thf('49', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.71          | ((sk_C_1) = (sk_B))
% 0.46/0.71          | ((sk_B) = (sk_D_1))
% 0.46/0.71          | ((sk_A) = (X0))
% 0.46/0.71          | ((sk_B) = (sk_D_1))
% 0.46/0.71          | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['41', '48'])).
% 0.46/0.71  thf('50', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((sk_A) = (X0)) | ((sk_B) = (sk_D_1)) | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['49'])).
% 0.46/0.71  thf('51', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((sk_A) = (X0)) | ((sk_B) = (sk_D_1)) | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['49'])).
% 0.46/0.71  thf('52', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (((X0) = (X1))
% 0.46/0.71          | ((sk_C_1) = (sk_B))
% 0.46/0.71          | ((sk_B) = (sk_D_1))
% 0.46/0.71          | ((sk_C_1) = (sk_B))
% 0.46/0.71          | ((sk_B) = (sk_D_1)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.71  thf('53', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (((sk_B) = (sk_D_1)) | ((sk_C_1) = (sk_B)) | ((X0) = (X1)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.71  thf('54', plain, ((((sk_B) = (sk_D_1)) | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('condensation', [status(thm)], ['53'])).
% 0.46/0.71  thf('55', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.46/0.71  thf('56', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i]:
% 0.46/0.71         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.71  thf('57', plain,
% 0.46/0.71      (![X16 : $i, X19 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X19 @ X16))),
% 0.46/0.71      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.71  thf('58', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.71  thf('59', plain,
% 0.46/0.71      (((r2_hidden @ sk_A @ (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['55', '58'])).
% 0.46/0.71  thf('60', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('61', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((sk_A) = (sk_D_1)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.71  thf('62', plain, (((sk_A) != (sk_D_1))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('63', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.46/0.71  thf('64', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['18', '20'])).
% 0.46/0.71  thf('65', plain,
% 0.46/0.71      (((r2_hidden @ sk_B @ (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['63', '64'])).
% 0.46/0.71  thf('66', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('67', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('clc', [status(thm)], ['65', '66'])).
% 0.46/0.71  thf('68', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['18', '20'])).
% 0.46/0.71  thf('69', plain, (((r2_hidden @ sk_B @ k1_xboole_0) | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.71  thf('70', plain,
% 0.46/0.71      (((r2_hidden @ sk_D_1 @ k1_xboole_0)
% 0.46/0.71        | ((sk_C_1) = (sk_B))
% 0.46/0.71        | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['54', '69'])).
% 0.46/0.71  thf('71', plain,
% 0.46/0.71      ((((sk_C_1) = (sk_B)) | (r2_hidden @ sk_D_1 @ k1_xboole_0))),
% 0.46/0.71      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.71  thf('72', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('clc', [status(thm)], ['65', '66'])).
% 0.46/0.71  thf('73', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.71  thf('74', plain,
% 0.46/0.71      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['72', '73'])).
% 0.46/0.71  thf('75', plain,
% 0.46/0.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.71  thf('76', plain,
% 0.46/0.71      ((((sk_C_1) = (sk_B)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.71  thf('77', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('78', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.46/0.71          | ((sk_C_1) = (sk_B))
% 0.46/0.71          | ((X0) = (sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.71  thf('79', plain,
% 0.46/0.71      ((((sk_C_1) = (sk_B)) | ((sk_D_1) = (sk_A)) | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['71', '78'])).
% 0.46/0.71  thf('80', plain, ((((sk_D_1) = (sk_A)) | ((sk_C_1) = (sk_B)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['79'])).
% 0.46/0.71  thf('81', plain, (((sk_A) != (sk_D_1))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('82', plain, (((sk_C_1) = (sk_B))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.46/0.71  thf('83', plain, (((sk_C_1) = (sk_B))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.46/0.71  thf('84', plain,
% 0.46/0.71      ((~ (r1_tarski @ (k2_tarski @ sk_C_1 @ sk_D_1) @ 
% 0.46/0.71           (k1_enumset1 @ sk_A @ sk_A @ sk_C_1))
% 0.46/0.71        | ((k2_tarski @ sk_C_1 @ sk_D_1) = (k1_enumset1 @ sk_A @ sk_A @ sk_C_1)))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '82', '83'])).
% 0.46/0.71  thf('85', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.71  thf('86', plain,
% 0.46/0.71      (![X16 : $i, X19 : $i]: (r2_hidden @ X16 @ (k2_tarski @ X19 @ X16))),
% 0.46/0.71      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.71  thf('87', plain,
% 0.46/0.71      (((r2_hidden @ sk_D_1 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['85', '86'])).
% 0.46/0.71  thf('88', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.46/0.71          | ((X2) = (X1))
% 0.46/0.71          | ((X2) = (X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['11', '13'])).
% 0.46/0.71  thf('89', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_D_1) = (sk_B))
% 0.46/0.71        | ((sk_D_1) = (sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.71  thf('90', plain, (((sk_A) != (sk_D_1))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('91', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_D_1) = (sk_B)))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.46/0.71  thf('92', plain, (((sk_C_1) = (sk_B))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.46/0.71  thf('93', plain, (((sk_C_1) = (sk_B))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.46/0.71  thf('94', plain, (((sk_C_1) = (sk_B))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.46/0.71  thf('95', plain, (((sk_C_1) = (sk_B))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.46/0.71  thf('96', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_D_1) = (sk_C_1)))),
% 0.46/0.71      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.46/0.71  thf('97', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['18', '20'])).
% 0.46/0.71  thf('98', plain,
% 0.46/0.71      (((r2_hidden @ sk_C_1 @ (k1_tarski @ sk_D_1))
% 0.46/0.71        | ((sk_D_1) = (sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['96', '97'])).
% 0.46/0.71  thf('99', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('100', plain,
% 0.46/0.71      ((((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((sk_D_1) = (sk_C_1))
% 0.46/0.71        | ((sk_C_1) = (sk_D_1)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.71  thf('101', plain,
% 0.46/0.71      ((((sk_D_1) = (sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['100'])).
% 0.46/0.71  thf('102', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.71  thf('103', plain,
% 0.46/0.71      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.46/0.71        | ((sk_D_1) = (sk_C_1)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['101', '102'])).
% 0.46/0.71  thf('104', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('105', plain,
% 0.46/0.71      ((((sk_D_1) = (sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.46/0.71        | ((sk_A) = (sk_C_1)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['103', '104'])).
% 0.46/0.71  thf('106', plain, (((sk_A) != (sk_C_1))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('107', plain,
% 0.46/0.71      ((((sk_D_1) = (sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 0.46/0.71  thf('108', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['18', '20'])).
% 0.46/0.71  thf('109', plain,
% 0.46/0.71      (((r2_hidden @ sk_C_1 @ k1_xboole_0) | ((sk_D_1) = (sk_C_1)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['107', '108'])).
% 0.46/0.71  thf('110', plain,
% 0.46/0.71      ((((sk_D_1) = (sk_C_1))
% 0.46/0.71        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 0.46/0.71  thf('111', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.71  thf('112', plain,
% 0.46/0.71      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_D_1) = (sk_C_1)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['110', '111'])).
% 0.46/0.71  thf('113', plain,
% 0.46/0.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.71  thf('114', plain,
% 0.46/0.71      ((((sk_D_1) = (sk_C_1)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['112', '113'])).
% 0.46/0.71  thf('115', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('116', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.46/0.71          | ((sk_D_1) = (sk_C_1))
% 0.46/0.71          | ((X0) = (sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['114', '115'])).
% 0.46/0.71  thf('117', plain,
% 0.46/0.71      ((((sk_D_1) = (sk_C_1)) | ((sk_C_1) = (sk_A)) | ((sk_D_1) = (sk_C_1)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['109', '116'])).
% 0.46/0.71  thf('118', plain, ((((sk_C_1) = (sk_A)) | ((sk_D_1) = (sk_C_1)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['117'])).
% 0.46/0.71  thf('119', plain, (((sk_A) != (sk_C_1))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('120', plain, (((sk_D_1) = (sk_C_1))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.46/0.71  thf(t94_enumset1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.71  thf('121', plain,
% 0.46/0.71      (![X27 : $i]:
% 0.46/0.71         ((k5_enumset1 @ X27 @ X27 @ X27 @ X27 @ X27 @ X27 @ X27)
% 0.46/0.71           = (k1_tarski @ X27))),
% 0.46/0.71      inference('cnf', [status(esa)], [t94_enumset1])).
% 0.46/0.71  thf(t89_enumset1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ B @ C ) =
% 0.46/0.71       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.71  thf('122', plain,
% 0.46/0.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.71         ((k5_enumset1 @ X24 @ X24 @ X24 @ X24 @ X24 @ X25 @ X26)
% 0.46/0.71           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 0.46/0.71      inference('cnf', [status(esa)], [t89_enumset1])).
% 0.46/0.71  thf('123', plain,
% 0.46/0.71      (![X27 : $i]: ((k1_enumset1 @ X27 @ X27 @ X27) = (k1_tarski @ X27))),
% 0.46/0.71      inference('demod', [status(thm)], ['121', '122'])).
% 0.46/0.71  thf('124', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i]:
% 0.46/0.71         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.71  thf('125', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['123', '124'])).
% 0.46/0.71  thf('126', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i]:
% 0.46/0.71         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.71  thf('127', plain,
% 0.46/0.71      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.46/0.71         ((r1_tarski @ X30 @ (k2_tarski @ X28 @ X31))
% 0.46/0.71          | ((X30) != (k1_tarski @ X31)))),
% 0.46/0.71      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.46/0.71  thf('128', plain,
% 0.46/0.71      (![X28 : $i, X31 : $i]:
% 0.46/0.71         (r1_tarski @ (k1_tarski @ X31) @ (k2_tarski @ X28 @ X31))),
% 0.46/0.71      inference('simplify', [status(thm)], ['127'])).
% 0.46/0.71  thf('129', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (r1_tarski @ (k1_tarski @ X0) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['126', '128'])).
% 0.46/0.71  thf('130', plain, (((sk_D_1) = (sk_C_1))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.46/0.71  thf('131', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['123', '124'])).
% 0.46/0.71  thf('132', plain,
% 0.46/0.71      (((k1_tarski @ sk_C_1) = (k1_enumset1 @ sk_A @ sk_A @ sk_C_1))),
% 0.46/0.71      inference('demod', [status(thm)],
% 0.46/0.71                ['84', '120', '125', '129', '130', '131'])).
% 0.46/0.71  thf('133', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.71  thf('134', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))),
% 0.46/0.71      inference('sup+', [status(thm)], ['132', '133'])).
% 0.46/0.71  thf('135', plain,
% 0.46/0.71      (![X11 : $i, X14 : $i]:
% 0.46/0.71         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.71  thf('136', plain, (((sk_A) = (sk_C_1))),
% 0.46/0.71      inference('sup-', [status(thm)], ['134', '135'])).
% 0.46/0.71  thf('137', plain, (((sk_A) != (sk_C_1))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('138', plain, ($false),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['136', '137'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
