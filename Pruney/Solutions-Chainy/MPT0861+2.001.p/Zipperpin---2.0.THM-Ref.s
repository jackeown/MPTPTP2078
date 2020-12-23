%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n9VduZQrjQ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:51 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  155 (1279 expanded)
%              Number of leaves         :   24 ( 386 expanded)
%              Depth                    :   37
%              Number of atoms          : 1361 (10865 expanded)
%              Number of equality atoms :  108 ( 672 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ ( k2_tarski @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k4_tarski @ X25 @ X26 ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ X27 ) @ X28 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ X27 ) @ X29 )
      | ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t11_mcart_1])).

thf('8',plain,(
    ! [X25: $i,X26: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X28 @ X29 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X25 @ X26 ) ) @ X29 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) ) @ X28 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('9',plain,(
    ! [X36: $i,X38: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X36 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X36 @ X37 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,(
    ! [X25: $i,X26: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X28 @ X29 ) )
      | ~ ( r2_hidden @ X26 @ X29 )
      | ~ ( r2_hidden @ X25 @ X28 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('17',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X28 @ X29 ) )
      | ~ ( r2_hidden @ X26 @ X29 )
      | ~ ( r2_hidden @ X25 @ X28 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('24',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X17 @ X16 )
      | ( X16
        = ( k4_xboole_0 @ X16 @ ( k2_tarski @ X15 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X17 @ X16 )
      | ( X16
        = ( k4_xboole_0 @ X16 @ ( k2_tarski @ X15 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('40',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X18 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X20 @ X19 )
      | ~ ( r1_tarski @ ( k2_tarski @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('47',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X18 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_C ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('67',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('69',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('71',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('73',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('75',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('80',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','86'])).

thf('88',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('90',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('92',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('97',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('99',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['88','99'])).

thf('101',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('102',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_mcart_1 @ X31 )
        = X30 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ X0 ) )
      | ( ( k1_tarski @ sk_B )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( ( k1_mcart_1 @ X1 )
        = ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) )
      = ( k1_mcart_1 @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','103'])).

thf('105',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X36 @ X37 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('106',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('110',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_mcart_1 @ X33 )
        = X35 )
      | ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X34 @ ( k1_tarski @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('111',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['112'])).

thf('114',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['107'])).

thf('117',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['115','116'])).

thf('118',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['108','117'])).

thf('119',plain,
    ( ( k1_tarski @ sk_B )
    = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['106','118'])).

thf('120',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_mcart_1 @ X31 )
        = X30 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ X0 ) )
      | ( ( k1_mcart_1 @ X1 )
        = ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ sk_B @ X0 ) )
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','121'])).

thf('123',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X36 @ X37 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('124',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['112'])).

thf('126',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['112'])).

thf('127',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['115','126'])).

thf('128',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['125','127'])).

thf('129',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n9VduZQrjQ
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.38/1.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.59  % Solved by: fo/fo7.sh
% 1.38/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.59  % done 1551 iterations in 1.141s
% 1.38/1.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.59  % SZS output start Refutation
% 1.38/1.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.38/1.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.38/1.59  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.38/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.38/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.38/1.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.38/1.59  thf(sk_C_type, type, sk_C: $i).
% 1.38/1.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.38/1.59  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.38/1.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.38/1.59  thf(t69_enumset1, axiom,
% 1.38/1.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.38/1.59  thf('0', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.38/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.38/1.59  thf(d10_xboole_0, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.38/1.59  thf('1', plain,
% 1.38/1.59      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.38/1.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.59  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.38/1.59      inference('simplify', [status(thm)], ['1'])).
% 1.38/1.59  thf(t38_zfmisc_1, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.38/1.59       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.38/1.59  thf('3', plain,
% 1.38/1.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.38/1.59         ((r2_hidden @ X18 @ X19)
% 1.38/1.59          | ~ (r1_tarski @ (k2_tarski @ X18 @ X20) @ X19))),
% 1.38/1.59      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.38/1.59  thf('4', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['2', '3'])).
% 1.38/1.59  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf(t11_mcart_1, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.38/1.59         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 1.38/1.59       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 1.38/1.59         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.38/1.59  thf('7', plain,
% 1.38/1.59      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.38/1.59         (((X27) != (k4_tarski @ X25 @ X26))
% 1.38/1.59          | ~ (r2_hidden @ (k1_mcart_1 @ X27) @ X28)
% 1.38/1.59          | ~ (r2_hidden @ (k2_mcart_1 @ X27) @ X29)
% 1.38/1.59          | (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 1.38/1.59      inference('cnf', [status(esa)], [t11_mcart_1])).
% 1.38/1.59  thf('8', plain,
% 1.38/1.59      (![X25 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 1.38/1.59         ((r2_hidden @ (k4_tarski @ X25 @ X26) @ (k2_zfmisc_1 @ X28 @ X29))
% 1.38/1.59          | ~ (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X25 @ X26)) @ X29)
% 1.38/1.59          | ~ (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X25 @ X26)) @ X28))),
% 1.38/1.59      inference('simplify', [status(thm)], ['7'])).
% 1.38/1.59  thf(t7_mcart_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 1.38/1.59       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 1.38/1.59  thf('9', plain,
% 1.38/1.59      (![X36 : $i, X38 : $i]: ((k2_mcart_1 @ (k4_tarski @ X36 @ X38)) = (X38))),
% 1.38/1.59      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.38/1.59  thf('10', plain,
% 1.38/1.59      (![X36 : $i, X37 : $i]: ((k1_mcart_1 @ (k4_tarski @ X36 @ X37)) = (X36))),
% 1.38/1.59      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.38/1.59  thf('11', plain,
% 1.38/1.59      (![X25 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 1.38/1.59         ((r2_hidden @ (k4_tarski @ X25 @ X26) @ (k2_zfmisc_1 @ X28 @ X29))
% 1.38/1.59          | ~ (r2_hidden @ X26 @ X29)
% 1.38/1.59          | ~ (r2_hidden @ X25 @ X28))),
% 1.38/1.59      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.38/1.59  thf('12', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X2 @ X1)
% 1.38/1.59          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 1.38/1.59             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['6', '11'])).
% 1.38/1.59  thf('13', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 1.38/1.59          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['5', '12'])).
% 1.38/1.59  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf(t17_mcart_1, conjecture,
% 1.38/1.59    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.59     ( ( r2_hidden @
% 1.38/1.59         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 1.38/1.59       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 1.38/1.59         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 1.38/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.59        ( ( r2_hidden @
% 1.38/1.59            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 1.38/1.59          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 1.38/1.59            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 1.38/1.59    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 1.38/1.59  thf('15', plain,
% 1.38/1.59      ((r2_hidden @ sk_A @ 
% 1.38/1.59        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 1.38/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.59  thf(t10_mcart_1, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.38/1.59       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.38/1.59         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.38/1.59  thf('16', plain,
% 1.38/1.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.38/1.59         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 1.38/1.59          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 1.38/1.59      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.38/1.59  thf('17', plain,
% 1.38/1.59      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 1.38/1.59      inference('sup-', [status(thm)], ['15', '16'])).
% 1.38/1.59  thf('18', plain,
% 1.38/1.59      (![X25 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 1.38/1.59         ((r2_hidden @ (k4_tarski @ X25 @ X26) @ (k2_zfmisc_1 @ X28 @ X29))
% 1.38/1.59          | ~ (r2_hidden @ X26 @ X29)
% 1.38/1.59          | ~ (r2_hidden @ X25 @ X28))),
% 1.38/1.59      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.38/1.59  thf('19', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X1 @ X0)
% 1.38/1.59          | (r2_hidden @ (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 1.38/1.59             (k2_zfmisc_1 @ X0 @ (k2_tarski @ sk_B @ sk_C))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['17', '18'])).
% 1.38/1.59  thf('20', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (r2_hidden @ (k4_tarski @ X0 @ (k1_mcart_1 @ sk_A)) @ 
% 1.38/1.59          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k2_tarski @ sk_B @ sk_C)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['14', '19'])).
% 1.38/1.59  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf('24', plain,
% 1.38/1.59      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 1.38/1.59      inference('sup-', [status(thm)], ['15', '16'])).
% 1.38/1.59  thf(t144_zfmisc_1, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.38/1.59          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.38/1.59  thf('25', plain,
% 1.38/1.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.38/1.59         ((r2_hidden @ X15 @ X16)
% 1.38/1.59          | (r2_hidden @ X17 @ X16)
% 1.38/1.59          | ((X16) = (k4_xboole_0 @ X16 @ (k2_tarski @ X15 @ X17))))),
% 1.38/1.59      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.38/1.59  thf(d5_xboole_0, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.38/1.59       ( ![D:$i]:
% 1.38/1.59         ( ( r2_hidden @ D @ C ) <=>
% 1.38/1.59           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.38/1.59  thf('26', plain,
% 1.38/1.59      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X4 @ X3)
% 1.38/1.59          | ~ (r2_hidden @ X4 @ X2)
% 1.38/1.59          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.38/1.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.38/1.59  thf('27', plain,
% 1.38/1.59      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X4 @ X2)
% 1.38/1.59          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.38/1.59      inference('simplify', [status(thm)], ['26'])).
% 1.38/1.59  thf('28', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X3 @ X0)
% 1.38/1.59          | (r2_hidden @ X1 @ X0)
% 1.38/1.59          | (r2_hidden @ X2 @ X0)
% 1.38/1.59          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['25', '27'])).
% 1.38/1.59  thf('29', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         ((r2_hidden @ sk_B @ X0)
% 1.38/1.59          | (r2_hidden @ sk_C @ X0)
% 1.38/1.59          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['24', '28'])).
% 1.38/1.59  thf('30', plain,
% 1.38/1.59      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['23', '29'])).
% 1.38/1.59  thf('31', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.38/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.38/1.59  thf('32', plain,
% 1.38/1.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.38/1.59         ((r2_hidden @ X15 @ X16)
% 1.38/1.59          | (r2_hidden @ X17 @ X16)
% 1.38/1.59          | ((X16) = (k4_xboole_0 @ X16 @ (k2_tarski @ X15 @ X17))))),
% 1.38/1.59      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.38/1.59  thf('33', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.38/1.59          | (r2_hidden @ X0 @ X1)
% 1.38/1.59          | (r2_hidden @ X0 @ X1))),
% 1.38/1.59      inference('sup+', [status(thm)], ['31', '32'])).
% 1.38/1.59  thf('34', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((r2_hidden @ X0 @ X1)
% 1.38/1.59          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.38/1.59      inference('simplify', [status(thm)], ['33'])).
% 1.38/1.59  thf('35', plain,
% 1.38/1.59      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X4 @ X2)
% 1.38/1.59          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.38/1.59      inference('simplify', [status(thm)], ['26'])).
% 1.38/1.59  thf('36', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X2 @ X0)
% 1.38/1.59          | (r2_hidden @ X1 @ X0)
% 1.38/1.59          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['34', '35'])).
% 1.38/1.59  thf('37', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 1.38/1.59          | ~ (r2_hidden @ sk_C @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['30', '36'])).
% 1.38/1.59  thf('38', plain,
% 1.38/1.59      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 1.38/1.59        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['22', '37'])).
% 1.38/1.59  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf('40', plain,
% 1.38/1.59      (![X18 : $i, X20 : $i, X21 : $i]:
% 1.38/1.59         ((r1_tarski @ (k2_tarski @ X18 @ X20) @ X21)
% 1.38/1.59          | ~ (r2_hidden @ X20 @ X21)
% 1.38/1.59          | ~ (r2_hidden @ X18 @ X21))),
% 1.38/1.59      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.38/1.59  thf('41', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.38/1.59          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['39', '40'])).
% 1.38/1.59  thf('42', plain,
% 1.38/1.59      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_C) @ 
% 1.38/1.59           (k1_tarski @ sk_C)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['38', '41'])).
% 1.38/1.59  thf('43', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.38/1.59      inference('simplify', [status(thm)], ['1'])).
% 1.38/1.59  thf('44', plain,
% 1.38/1.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.38/1.59         ((r2_hidden @ X20 @ X19)
% 1.38/1.59          | ~ (r1_tarski @ (k2_tarski @ X18 @ X20) @ X19))),
% 1.38/1.59      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.38/1.59  thf('45', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['43', '44'])).
% 1.38/1.59  thf('46', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['2', '3'])).
% 1.38/1.59  thf('47', plain,
% 1.38/1.59      (![X18 : $i, X20 : $i, X21 : $i]:
% 1.38/1.59         ((r1_tarski @ (k2_tarski @ X18 @ X20) @ X21)
% 1.38/1.59          | ~ (r2_hidden @ X20 @ X21)
% 1.38/1.59          | ~ (r2_hidden @ X18 @ X21))),
% 1.38/1.59      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.38/1.59  thf('48', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.38/1.59          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['46', '47'])).
% 1.38/1.59  thf('49', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['45', '48'])).
% 1.38/1.59  thf('50', plain,
% 1.38/1.59      (![X6 : $i, X8 : $i]:
% 1.38/1.59         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.38/1.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.59  thf('51', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 1.38/1.59          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['49', '50'])).
% 1.38/1.59  thf('52', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['45', '48'])).
% 1.38/1.59  thf('53', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.38/1.59      inference('demod', [status(thm)], ['51', '52'])).
% 1.38/1.59  thf('54', plain,
% 1.38/1.59      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 1.38/1.59           (k1_tarski @ sk_C)))),
% 1.38/1.59      inference('demod', [status(thm)], ['42', '53'])).
% 1.38/1.59  thf('55', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.38/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.38/1.59  thf('56', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['2', '3'])).
% 1.38/1.59  thf('57', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.38/1.59          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['46', '47'])).
% 1.38/1.59  thf('58', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['56', '57'])).
% 1.38/1.59  thf('59', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 1.38/1.59      inference('sup+', [status(thm)], ['55', '58'])).
% 1.38/1.59  thf('60', plain,
% 1.38/1.59      (![X6 : $i, X8 : $i]:
% 1.38/1.59         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.38/1.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.59  thf('61', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.38/1.59          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['59', '60'])).
% 1.38/1.59  thf('62', plain,
% 1.38/1.59      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['54', '61'])).
% 1.38/1.59  thf('63', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X2 @ X0)
% 1.38/1.59          | (r2_hidden @ X1 @ X0)
% 1.38/1.59          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['34', '35'])).
% 1.38/1.59  thf('64', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.38/1.59          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 1.38/1.59          | ~ (r2_hidden @ sk_B @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['62', '63'])).
% 1.38/1.59  thf('65', plain,
% 1.38/1.59      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 1.38/1.59        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['21', '64'])).
% 1.38/1.59  thf('66', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.38/1.59          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['39', '40'])).
% 1.38/1.59  thf('67', plain,
% 1.38/1.59      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.38/1.59        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_B) @ 
% 1.38/1.59           (k1_tarski @ sk_B)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['65', '66'])).
% 1.38/1.59  thf('68', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.38/1.59      inference('demod', [status(thm)], ['51', '52'])).
% 1.38/1.59  thf('69', plain,
% 1.38/1.59      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.38/1.59        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 1.38/1.59           (k1_tarski @ sk_B)))),
% 1.38/1.59      inference('demod', [status(thm)], ['67', '68'])).
% 1.38/1.59  thf('70', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.38/1.59          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['59', '60'])).
% 1.38/1.59  thf('71', plain,
% 1.38/1.59      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.38/1.59        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['69', '70'])).
% 1.38/1.59  thf('72', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf('73', plain,
% 1.38/1.59      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.38/1.59        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['69', '70'])).
% 1.38/1.59  thf('74', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['43', '44'])).
% 1.38/1.59  thf('75', plain,
% 1.38/1.59      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 1.38/1.59        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['73', '74'])).
% 1.38/1.59  thf('76', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X2 @ X0)
% 1.38/1.59          | (r2_hidden @ X1 @ X0)
% 1.38/1.59          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['34', '35'])).
% 1.38/1.59  thf('77', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 1.38/1.59          | (r2_hidden @ sk_C @ X0)
% 1.38/1.59          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['75', '76'])).
% 1.38/1.59  thf('78', plain,
% 1.38/1.59      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['72', '77'])).
% 1.38/1.59  thf('79', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.38/1.59          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['39', '40'])).
% 1.38/1.59  thf('80', plain,
% 1.38/1.59      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 1.38/1.59        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 1.38/1.59           (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['78', '79'])).
% 1.38/1.59  thf('81', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.38/1.59      inference('demod', [status(thm)], ['51', '52'])).
% 1.38/1.59  thf('82', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 1.38/1.59      inference('sup+', [status(thm)], ['55', '58'])).
% 1.38/1.59  thf('83', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['81', '82'])).
% 1.38/1.59  thf('84', plain,
% 1.38/1.59      (![X6 : $i, X8 : $i]:
% 1.38/1.59         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.38/1.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.38/1.59  thf('85', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 1.38/1.59          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['83', '84'])).
% 1.38/1.59  thf('86', plain,
% 1.38/1.59      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 1.38/1.59        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 1.38/1.59            = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['80', '85'])).
% 1.38/1.59  thf('87', plain,
% 1.38/1.59      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 1.38/1.59        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['71', '86'])).
% 1.38/1.59  thf('88', plain,
% 1.38/1.59      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 1.38/1.59        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('simplify', [status(thm)], ['87'])).
% 1.38/1.59  thf('89', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['0', '4'])).
% 1.38/1.59  thf('90', plain,
% 1.38/1.59      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 1.38/1.59        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('simplify', [status(thm)], ['87'])).
% 1.38/1.59  thf('91', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['43', '44'])).
% 1.38/1.59  thf('92', plain,
% 1.38/1.59      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 1.38/1.59        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup+', [status(thm)], ['90', '91'])).
% 1.38/1.59  thf('93', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X2 @ X0)
% 1.38/1.59          | (r2_hidden @ X1 @ X0)
% 1.38/1.59          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['34', '35'])).
% 1.38/1.59  thf('94', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59          | (r2_hidden @ sk_B @ X0)
% 1.38/1.59          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['92', '93'])).
% 1.38/1.59  thf('95', plain,
% 1.38/1.59      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['89', '94'])).
% 1.38/1.59  thf('96', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.38/1.59          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['39', '40'])).
% 1.38/1.59  thf('97', plain,
% 1.38/1.59      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 1.38/1.59           (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['95', '96'])).
% 1.38/1.59  thf('98', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 1.38/1.59          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['83', '84'])).
% 1.38/1.59  thf('99', plain,
% 1.38/1.59      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A))
% 1.38/1.59            = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['97', '98'])).
% 1.38/1.59  thf('100', plain,
% 1.38/1.59      ((((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup+', [status(thm)], ['88', '99'])).
% 1.38/1.59  thf('101', plain,
% 1.38/1.59      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('simplify', [status(thm)], ['100'])).
% 1.38/1.59  thf(t12_mcart_1, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 1.38/1.59       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 1.38/1.59         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.38/1.59  thf('102', plain,
% 1.38/1.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.38/1.59         (((k1_mcart_1 @ X31) = (X30))
% 1.38/1.59          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ (k1_tarski @ X30) @ X32)))),
% 1.38/1.59      inference('cnf', [status(esa)], [t12_mcart_1])).
% 1.38/1.59  thf('103', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ X0))
% 1.38/1.59          | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59          | ((k1_mcart_1 @ X1) = (k1_mcart_1 @ sk_A)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['101', '102'])).
% 1.38/1.59  thf('104', plain,
% 1.38/1.59      ((((k1_mcart_1 @ (k4_tarski @ sk_C @ (k1_mcart_1 @ sk_A)))
% 1.38/1.59          = (k1_mcart_1 @ sk_A))
% 1.38/1.59        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['20', '103'])).
% 1.38/1.59  thf('105', plain,
% 1.38/1.59      (![X36 : $i, X37 : $i]: ((k1_mcart_1 @ (k4_tarski @ X36 @ X37)) = (X36))),
% 1.38/1.59      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.38/1.59  thf('106', plain,
% 1.38/1.59      ((((sk_C) = (k1_mcart_1 @ sk_A))
% 1.38/1.59        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.38/1.59      inference('demod', [status(thm)], ['104', '105'])).
% 1.38/1.59  thf('107', plain,
% 1.38/1.59      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 1.38/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.59  thf('108', plain,
% 1.38/1.59      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 1.38/1.59         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 1.38/1.59      inference('split', [status(esa)], ['107'])).
% 1.38/1.59  thf('109', plain,
% 1.38/1.59      ((r2_hidden @ sk_A @ 
% 1.38/1.59        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 1.38/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.59  thf(t13_mcart_1, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 1.38/1.59       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.38/1.59         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 1.38/1.59  thf('110', plain,
% 1.38/1.59      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.38/1.59         (((k2_mcart_1 @ X33) = (X35))
% 1.38/1.59          | ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X34 @ (k1_tarski @ X35))))),
% 1.38/1.59      inference('cnf', [status(esa)], [t13_mcart_1])).
% 1.38/1.59  thf('111', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1))),
% 1.38/1.59      inference('sup-', [status(thm)], ['109', '110'])).
% 1.38/1.59  thf('112', plain,
% 1.38/1.59      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 1.38/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.59  thf('113', plain,
% 1.38/1.59      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 1.38/1.59         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 1.38/1.59      inference('split', [status(esa)], ['112'])).
% 1.38/1.59  thf('114', plain,
% 1.38/1.59      ((((sk_D_1) != (sk_D_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 1.38/1.59      inference('sup-', [status(thm)], ['111', '113'])).
% 1.38/1.59  thf('115', plain, ((((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 1.38/1.59      inference('simplify', [status(thm)], ['114'])).
% 1.38/1.59  thf('116', plain,
% 1.38/1.59      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 1.38/1.59       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 1.38/1.59      inference('split', [status(esa)], ['107'])).
% 1.38/1.59  thf('117', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 1.38/1.59      inference('sat_resolution*', [status(thm)], ['115', '116'])).
% 1.38/1.59  thf('118', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 1.38/1.59      inference('simpl_trail', [status(thm)], ['108', '117'])).
% 1.38/1.59  thf('119', plain, (((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 1.38/1.59      inference('simplify_reflect-', [status(thm)], ['106', '118'])).
% 1.38/1.59  thf('120', plain,
% 1.38/1.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.38/1.59         (((k1_mcart_1 @ X31) = (X30))
% 1.38/1.59          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ (k1_tarski @ X30) @ X32)))),
% 1.38/1.59      inference('cnf', [status(esa)], [t12_mcart_1])).
% 1.38/1.59  thf('121', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ X0))
% 1.38/1.59          | ((k1_mcart_1 @ X1) = (k1_mcart_1 @ sk_A)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['119', '120'])).
% 1.38/1.59  thf('122', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         ((k1_mcart_1 @ (k4_tarski @ sk_B @ X0)) = (k1_mcart_1 @ sk_A))),
% 1.38/1.59      inference('sup-', [status(thm)], ['13', '121'])).
% 1.38/1.59  thf('123', plain,
% 1.38/1.59      (![X36 : $i, X37 : $i]: ((k1_mcart_1 @ (k4_tarski @ X36 @ X37)) = (X36))),
% 1.38/1.59      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.38/1.59  thf('124', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 1.38/1.59      inference('demod', [status(thm)], ['122', '123'])).
% 1.38/1.59  thf('125', plain,
% 1.38/1.59      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 1.38/1.59         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 1.38/1.59      inference('split', [status(esa)], ['112'])).
% 1.38/1.59  thf('126', plain,
% 1.38/1.59      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 1.38/1.59       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 1.38/1.59      inference('split', [status(esa)], ['112'])).
% 1.38/1.59  thf('127', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 1.38/1.59      inference('sat_resolution*', [status(thm)], ['115', '126'])).
% 1.38/1.59  thf('128', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 1.38/1.59      inference('simpl_trail', [status(thm)], ['125', '127'])).
% 1.38/1.59  thf('129', plain, ($false),
% 1.38/1.59      inference('simplify_reflect-', [status(thm)], ['124', '128'])).
% 1.38/1.59  
% 1.38/1.59  % SZS output end Refutation
% 1.38/1.59  
% 1.38/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
