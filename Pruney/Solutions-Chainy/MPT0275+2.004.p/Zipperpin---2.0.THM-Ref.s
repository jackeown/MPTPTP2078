%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c7Mwia0WJq

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:37 EST 2020

% Result     : Theorem 36.85s
% Output     : Refutation 36.85s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 379 expanded)
%              Number of leaves         :   25 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  935 (3591 expanded)
%              Number of equality atoms :   87 ( 322 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X54: $i,X56: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X54 ) @ X56 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k2_tarski @ X46 @ X47 )
      = ( k2_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('11',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r2_hidden @ X54 @ X55 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X54 ) @ X55 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['8','24','31','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['6','33'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('36',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k2_xboole_0 @ X0 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('47',plain,(
    ! [X54: $i,X56: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X54 ) @ X56 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('50',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('53',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['8','24','31','52'])).

thf('54',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('56',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('57',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('58',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('63',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('72',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['56','81'])).

thf('83',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C_1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','84'])).

thf('86',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k2_tarski @ X46 @ X47 )
      = ( k2_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('87',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('89',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['8','24','31'])).

thf('90',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c7Mwia0WJq
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 36.85/37.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 36.85/37.05  % Solved by: fo/fo7.sh
% 36.85/37.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.85/37.05  % done 20302 iterations in 36.616s
% 36.85/37.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 36.85/37.05  % SZS output start Refutation
% 36.85/37.05  thf(sk_A_type, type, sk_A: $i).
% 36.85/37.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 36.85/37.05  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 36.85/37.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 36.85/37.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 36.85/37.05  thf(sk_B_type, type, sk_B: $i).
% 36.85/37.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 36.85/37.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.85/37.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 36.85/37.05  thf(sk_C_1_type, type, sk_C_1: $i).
% 36.85/37.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 36.85/37.05  thf(t73_zfmisc_1, conjecture,
% 36.85/37.05    (![A:$i,B:$i,C:$i]:
% 36.85/37.05     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 36.85/37.05       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 36.85/37.05  thf(zf_stmt_0, negated_conjecture,
% 36.85/37.05    (~( ![A:$i,B:$i,C:$i]:
% 36.85/37.05        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 36.85/37.05          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 36.85/37.05    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 36.85/37.05  thf('0', plain,
% 36.85/37.05      (((r2_hidden @ sk_B @ sk_C_1)
% 36.85/37.05        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.05  thf('1', plain,
% 36.85/37.05      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 36.85/37.05      inference('split', [status(esa)], ['0'])).
% 36.85/37.05  thf(l35_zfmisc_1, axiom,
% 36.85/37.05    (![A:$i,B:$i]:
% 36.85/37.05     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 36.85/37.05       ( r2_hidden @ A @ B ) ))).
% 36.85/37.05  thf('2', plain,
% 36.85/37.05      (![X54 : $i, X56 : $i]:
% 36.85/37.05         (((k4_xboole_0 @ (k1_tarski @ X54) @ X56) = (k1_xboole_0))
% 36.85/37.05          | ~ (r2_hidden @ X54 @ X56))),
% 36.85/37.05      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 36.85/37.05  thf('3', plain,
% 36.85/37.05      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 36.85/37.05         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['1', '2'])).
% 36.85/37.05  thf(l32_xboole_1, axiom,
% 36.85/37.05    (![A:$i,B:$i]:
% 36.85/37.05     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 36.85/37.05  thf('4', plain,
% 36.85/37.05      (![X13 : $i, X14 : $i]:
% 36.85/37.05         ((r1_tarski @ X13 @ X14)
% 36.85/37.05          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.85/37.05  thf('5', plain,
% 36.85/37.05      (((((k1_xboole_0) != (k1_xboole_0))
% 36.85/37.05         | (r1_tarski @ (k1_tarski @ sk_B) @ sk_C_1)))
% 36.85/37.05         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['3', '4'])).
% 36.85/37.05  thf('6', plain,
% 36.85/37.05      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C_1))
% 36.85/37.05         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 36.85/37.05      inference('simplify', [status(thm)], ['5'])).
% 36.85/37.05  thf('7', plain,
% 36.85/37.05      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 36.85/37.05        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 36.85/37.05        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.05  thf('8', plain,
% 36.85/37.05      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 36.85/37.05       ~ ((r2_hidden @ sk_B @ sk_C_1)) | ~ ((r2_hidden @ sk_A @ sk_C_1))),
% 36.85/37.05      inference('split', [status(esa)], ['7'])).
% 36.85/37.05  thf(t41_enumset1, axiom,
% 36.85/37.05    (![A:$i,B:$i]:
% 36.85/37.05     ( ( k2_tarski @ A @ B ) =
% 36.85/37.05       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 36.85/37.05  thf('9', plain,
% 36.85/37.05      (![X46 : $i, X47 : $i]:
% 36.85/37.05         ((k2_tarski @ X46 @ X47)
% 36.85/37.05           = (k2_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X47)))),
% 36.85/37.05      inference('cnf', [status(esa)], [t41_enumset1])).
% 36.85/37.05  thf(t46_xboole_1, axiom,
% 36.85/37.05    (![A:$i,B:$i]:
% 36.85/37.05     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 36.85/37.05  thf('10', plain,
% 36.85/37.05      (![X24 : $i, X25 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X24 @ (k2_xboole_0 @ X24 @ X25)) = (k1_xboole_0))),
% 36.85/37.05      inference('cnf', [status(esa)], [t46_xboole_1])).
% 36.85/37.05  thf('11', plain,
% 36.85/37.05      (![X54 : $i, X55 : $i]:
% 36.85/37.05         ((r2_hidden @ X54 @ X55)
% 36.85/37.05          | ((k4_xboole_0 @ (k1_tarski @ X54) @ X55) != (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 36.85/37.05  thf('12', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]:
% 36.85/37.05         (((k1_xboole_0) != (k1_xboole_0))
% 36.85/37.05          | (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['10', '11'])).
% 36.85/37.05  thf('13', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]:
% 36.85/37.05         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 36.85/37.05      inference('simplify', [status(thm)], ['12'])).
% 36.85/37.05  thf('14', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 36.85/37.05      inference('sup+', [status(thm)], ['9', '13'])).
% 36.85/37.05  thf('15', plain,
% 36.85/37.05      (((r2_hidden @ sk_A @ sk_C_1)
% 36.85/37.05        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.05  thf('16', plain,
% 36.85/37.05      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 36.85/37.05         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 36.85/37.05                = (k1_xboole_0))))),
% 36.85/37.05      inference('split', [status(esa)], ['15'])).
% 36.85/37.05  thf('17', plain,
% 36.85/37.05      (![X13 : $i, X14 : $i]:
% 36.85/37.05         ((r1_tarski @ X13 @ X14)
% 36.85/37.05          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.85/37.05  thf('18', plain,
% 36.85/37.05      (((((k1_xboole_0) != (k1_xboole_0))
% 36.85/37.05         | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))
% 36.85/37.05         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 36.85/37.05                = (k1_xboole_0))))),
% 36.85/37.05      inference('sup-', [status(thm)], ['16', '17'])).
% 36.85/37.05  thf('19', plain,
% 36.85/37.05      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 36.85/37.05         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 36.85/37.05                = (k1_xboole_0))))),
% 36.85/37.05      inference('simplify', [status(thm)], ['18'])).
% 36.85/37.05  thf(d3_tarski, axiom,
% 36.85/37.05    (![A:$i,B:$i]:
% 36.85/37.05     ( ( r1_tarski @ A @ B ) <=>
% 36.85/37.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 36.85/37.05  thf('20', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.85/37.05         (~ (r2_hidden @ X0 @ X1)
% 36.85/37.05          | (r2_hidden @ X0 @ X2)
% 36.85/37.05          | ~ (r1_tarski @ X1 @ X2))),
% 36.85/37.05      inference('cnf', [status(esa)], [d3_tarski])).
% 36.85/37.05  thf('21', plain,
% 36.85/37.05      ((![X0 : $i]:
% 36.85/37.05          ((r2_hidden @ X0 @ sk_C_1)
% 36.85/37.05           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 36.85/37.05         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 36.85/37.05                = (k1_xboole_0))))),
% 36.85/37.05      inference('sup-', [status(thm)], ['19', '20'])).
% 36.85/37.05  thf('22', plain,
% 36.85/37.05      (((r2_hidden @ sk_A @ sk_C_1))
% 36.85/37.05         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 36.85/37.05                = (k1_xboole_0))))),
% 36.85/37.05      inference('sup-', [status(thm)], ['14', '21'])).
% 36.85/37.05  thf('23', plain,
% 36.85/37.05      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 36.85/37.05      inference('split', [status(esa)], ['7'])).
% 36.85/37.05  thf('24', plain,
% 36.85/37.05      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 36.85/37.05       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['22', '23'])).
% 36.85/37.05  thf(commutativity_k2_tarski, axiom,
% 36.85/37.05    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 36.85/37.05  thf('25', plain,
% 36.85/37.05      (![X32 : $i, X33 : $i]:
% 36.85/37.05         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 36.85/37.05      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 36.85/37.05  thf('26', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 36.85/37.05      inference('sup+', [status(thm)], ['9', '13'])).
% 36.85/37.05  thf('27', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 36.85/37.05      inference('sup+', [status(thm)], ['25', '26'])).
% 36.85/37.05  thf('28', plain,
% 36.85/37.05      ((![X0 : $i]:
% 36.85/37.05          ((r2_hidden @ X0 @ sk_C_1)
% 36.85/37.05           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 36.85/37.05         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 36.85/37.05                = (k1_xboole_0))))),
% 36.85/37.05      inference('sup-', [status(thm)], ['19', '20'])).
% 36.85/37.05  thf('29', plain,
% 36.85/37.05      (((r2_hidden @ sk_B @ sk_C_1))
% 36.85/37.05         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 36.85/37.05                = (k1_xboole_0))))),
% 36.85/37.05      inference('sup-', [status(thm)], ['27', '28'])).
% 36.85/37.05  thf('30', plain,
% 36.85/37.05      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 36.85/37.05      inference('split', [status(esa)], ['7'])).
% 36.85/37.05  thf('31', plain,
% 36.85/37.05      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 36.85/37.05       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['29', '30'])).
% 36.85/37.05  thf('32', plain,
% 36.85/37.05      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 36.85/37.05       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 36.85/37.05      inference('split', [status(esa)], ['0'])).
% 36.85/37.05  thf('33', plain, (((r2_hidden @ sk_B @ sk_C_1))),
% 36.85/37.05      inference('sat_resolution*', [status(thm)], ['8', '24', '31', '32'])).
% 36.85/37.05  thf('34', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_C_1)),
% 36.85/37.05      inference('simpl_trail', [status(thm)], ['6', '33'])).
% 36.85/37.05  thf(t45_xboole_1, axiom,
% 36.85/37.05    (![A:$i,B:$i]:
% 36.85/37.05     ( ( r1_tarski @ A @ B ) =>
% 36.85/37.05       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 36.85/37.05  thf('35', plain,
% 36.85/37.05      (![X22 : $i, X23 : $i]:
% 36.85/37.05         (((X23) = (k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))
% 36.85/37.05          | ~ (r1_tarski @ X22 @ X23))),
% 36.85/37.05      inference('cnf', [status(esa)], [t45_xboole_1])).
% 36.85/37.05  thf('36', plain,
% 36.85/37.05      (((sk_C_1)
% 36.85/37.05         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ 
% 36.85/37.05            (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B))))),
% 36.85/37.05      inference('sup-', [status(thm)], ['34', '35'])).
% 36.85/37.05  thf(t41_xboole_1, axiom,
% 36.85/37.05    (![A:$i,B:$i,C:$i]:
% 36.85/37.05     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 36.85/37.05       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 36.85/37.05  thf('37', plain,
% 36.85/37.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 36.85/37.05           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 36.85/37.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 36.85/37.05  thf('38', plain,
% 36.85/37.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 36.85/37.05           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 36.85/37.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 36.85/37.05  thf('39', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 36.85/37.05           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 36.85/37.05      inference('sup+', [status(thm)], ['37', '38'])).
% 36.85/37.05  thf('40', plain,
% 36.85/37.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 36.85/37.05           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 36.85/37.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 36.85/37.05  thf('41', plain,
% 36.85/37.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 36.85/37.05           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 36.85/37.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 36.85/37.05  thf('42', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 36.85/37.05           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 36.85/37.05      inference('demod', [status(thm)], ['39', '40', '41'])).
% 36.85/37.05  thf('43', plain,
% 36.85/37.05      (![X24 : $i, X25 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X24 @ (k2_xboole_0 @ X24 @ X25)) = (k1_xboole_0))),
% 36.85/37.05      inference('cnf', [status(esa)], [t46_xboole_1])).
% 36.85/37.05  thf('44', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 36.85/37.05           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 36.85/37.05      inference('sup+', [status(thm)], ['42', '43'])).
% 36.85/37.05  thf('45', plain,
% 36.85/37.05      (![X0 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k1_tarski @ sk_B)) @ 
% 36.85/37.05           (k2_xboole_0 @ X0 @ sk_C_1)) = (k1_xboole_0))),
% 36.85/37.05      inference('sup+', [status(thm)], ['36', '44'])).
% 36.85/37.05  thf('46', plain,
% 36.85/37.05      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 36.85/37.05      inference('split', [status(esa)], ['15'])).
% 36.85/37.05  thf('47', plain,
% 36.85/37.05      (![X54 : $i, X56 : $i]:
% 36.85/37.05         (((k4_xboole_0 @ (k1_tarski @ X54) @ X56) = (k1_xboole_0))
% 36.85/37.05          | ~ (r2_hidden @ X54 @ X56))),
% 36.85/37.05      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 36.85/37.05  thf('48', plain,
% 36.85/37.05      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (k1_xboole_0)))
% 36.85/37.05         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['46', '47'])).
% 36.85/37.05  thf('49', plain,
% 36.85/37.05      (![X13 : $i, X14 : $i]:
% 36.85/37.05         ((r1_tarski @ X13 @ X14)
% 36.85/37.05          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.85/37.05  thf('50', plain,
% 36.85/37.05      (((((k1_xboole_0) != (k1_xboole_0))
% 36.85/37.05         | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)))
% 36.85/37.05         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['48', '49'])).
% 36.85/37.05  thf('51', plain,
% 36.85/37.05      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1))
% 36.85/37.05         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 36.85/37.05      inference('simplify', [status(thm)], ['50'])).
% 36.85/37.05  thf('52', plain,
% 36.85/37.05      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 36.85/37.05       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 36.85/37.05      inference('split', [status(esa)], ['15'])).
% 36.85/37.05  thf('53', plain, (((r2_hidden @ sk_A @ sk_C_1))),
% 36.85/37.05      inference('sat_resolution*', [status(thm)], ['8', '24', '31', '52'])).
% 36.85/37.05  thf('54', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)),
% 36.85/37.05      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 36.85/37.05  thf('55', plain,
% 36.85/37.05      (![X22 : $i, X23 : $i]:
% 36.85/37.05         (((X23) = (k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))
% 36.85/37.05          | ~ (r1_tarski @ X22 @ X23))),
% 36.85/37.05      inference('cnf', [status(esa)], [t45_xboole_1])).
% 36.85/37.05  thf('56', plain,
% 36.85/37.05      (((sk_C_1)
% 36.85/37.05         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 36.85/37.05            (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 36.85/37.05      inference('sup-', [status(thm)], ['54', '55'])).
% 36.85/37.05  thf(t79_xboole_1, axiom,
% 36.85/37.05    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 36.85/37.05  thf('57', plain,
% 36.85/37.05      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 36.85/37.05      inference('cnf', [status(esa)], [t79_xboole_1])).
% 36.85/37.05  thf(t83_xboole_1, axiom,
% 36.85/37.05    (![A:$i,B:$i]:
% 36.85/37.05     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 36.85/37.05  thf('58', plain,
% 36.85/37.05      (![X29 : $i, X30 : $i]:
% 36.85/37.05         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 36.85/37.05      inference('cnf', [status(esa)], [t83_xboole_1])).
% 36.85/37.05  thf('59', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 36.85/37.05           = (k4_xboole_0 @ X1 @ X0))),
% 36.85/37.05      inference('sup-', [status(thm)], ['57', '58'])).
% 36.85/37.05  thf('60', plain,
% 36.85/37.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 36.85/37.05           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 36.85/37.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 36.85/37.05  thf('61', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 36.85/37.05           = (k4_xboole_0 @ X1 @ X0))),
% 36.85/37.05      inference('demod', [status(thm)], ['59', '60'])).
% 36.85/37.05  thf(t1_boole, axiom,
% 36.85/37.05    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 36.85/37.05  thf('62', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 36.85/37.05      inference('cnf', [status(esa)], [t1_boole])).
% 36.85/37.05  thf('63', plain,
% 36.85/37.05      (![X24 : $i, X25 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X24 @ (k2_xboole_0 @ X24 @ X25)) = (k1_xboole_0))),
% 36.85/37.05      inference('cnf', [status(esa)], [t46_xboole_1])).
% 36.85/37.05  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 36.85/37.05      inference('sup+', [status(thm)], ['62', '63'])).
% 36.85/37.05  thf('65', plain,
% 36.85/37.05      (![X0 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0) = (k1_xboole_0))),
% 36.85/37.05      inference('sup+', [status(thm)], ['61', '64'])).
% 36.85/37.05  thf('66', plain,
% 36.85/37.05      (![X13 : $i, X14 : $i]:
% 36.85/37.05         ((r1_tarski @ X13 @ X14)
% 36.85/37.05          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.85/37.05  thf('67', plain,
% 36.85/37.05      (![X0 : $i]:
% 36.85/37.05         (((k1_xboole_0) != (k1_xboole_0))
% 36.85/37.05          | (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 36.85/37.05      inference('sup-', [status(thm)], ['65', '66'])).
% 36.85/37.05  thf('68', plain, (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0)),
% 36.85/37.05      inference('simplify', [status(thm)], ['67'])).
% 36.85/37.05  thf(d10_xboole_0, axiom,
% 36.85/37.05    (![A:$i,B:$i]:
% 36.85/37.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.85/37.05  thf('69', plain,
% 36.85/37.05      (![X10 : $i, X12 : $i]:
% 36.85/37.05         (((X10) = (X12))
% 36.85/37.05          | ~ (r1_tarski @ X12 @ X10)
% 36.85/37.05          | ~ (r1_tarski @ X10 @ X12))),
% 36.85/37.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.85/37.05  thf('70', plain,
% 36.85/37.05      (![X0 : $i]:
% 36.85/37.05         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X0))
% 36.85/37.05          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['68', '69'])).
% 36.85/37.05  thf(t36_xboole_1, axiom,
% 36.85/37.05    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 36.85/37.05  thf('71', plain,
% 36.85/37.05      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 36.85/37.05      inference('cnf', [status(esa)], [t36_xboole_1])).
% 36.85/37.05  thf('72', plain,
% 36.85/37.05      (![X13 : $i, X15 : $i]:
% 36.85/37.05         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 36.85/37.05          | ~ (r1_tarski @ X13 @ X15))),
% 36.85/37.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.85/37.05  thf('73', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 36.85/37.05      inference('sup-', [status(thm)], ['71', '72'])).
% 36.85/37.05  thf('74', plain,
% 36.85/37.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 36.85/37.05           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 36.85/37.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 36.85/37.05  thf('75', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 36.85/37.05      inference('demod', [status(thm)], ['73', '74'])).
% 36.85/37.05  thf('76', plain,
% 36.85/37.05      (![X13 : $i, X14 : $i]:
% 36.85/37.05         ((r1_tarski @ X13 @ X14)
% 36.85/37.05          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 36.85/37.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 36.85/37.05  thf('77', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]:
% 36.85/37.05         (((k1_xboole_0) != (k1_xboole_0))
% 36.85/37.05          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 36.85/37.05      inference('sup-', [status(thm)], ['75', '76'])).
% 36.85/37.05  thf('78', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 36.85/37.05      inference('simplify', [status(thm)], ['77'])).
% 36.85/37.05  thf('79', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 36.85/37.05      inference('demod', [status(thm)], ['70', '78'])).
% 36.85/37.05  thf('80', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 36.85/37.05           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 36.85/37.05      inference('demod', [status(thm)], ['39', '40', '41'])).
% 36.85/37.05  thf('81', plain,
% 36.85/37.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))
% 36.85/37.05           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 36.85/37.05      inference('sup+', [status(thm)], ['79', '80'])).
% 36.85/37.05  thf('82', plain,
% 36.85/37.05      (![X0 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X0 @ 
% 36.85/37.05           (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 36.85/37.05            (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))
% 36.85/37.05           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1)))),
% 36.85/37.05      inference('sup+', [status(thm)], ['56', '81'])).
% 36.85/37.05  thf('83', plain,
% 36.85/37.05      (((sk_C_1)
% 36.85/37.05         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 36.85/37.05            (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 36.85/37.05      inference('sup-', [status(thm)], ['54', '55'])).
% 36.85/37.05  thf('84', plain,
% 36.85/37.05      (![X0 : $i]:
% 36.85/37.05         ((k4_xboole_0 @ X0 @ sk_C_1)
% 36.85/37.05           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1)))),
% 36.85/37.05      inference('demod', [status(thm)], ['82', '83'])).
% 36.85/37.05  thf('85', plain,
% 36.85/37.05      (((k4_xboole_0 @ 
% 36.85/37.05         (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ sk_C_1)
% 36.85/37.05         = (k1_xboole_0))),
% 36.85/37.05      inference('sup+', [status(thm)], ['45', '84'])).
% 36.85/37.05  thf('86', plain,
% 36.85/37.05      (![X46 : $i, X47 : $i]:
% 36.85/37.05         ((k2_tarski @ X46 @ X47)
% 36.85/37.05           = (k2_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X47)))),
% 36.85/37.05      inference('cnf', [status(esa)], [t41_enumset1])).
% 36.85/37.05  thf('87', plain,
% 36.85/37.05      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 36.85/37.05      inference('demod', [status(thm)], ['85', '86'])).
% 36.85/37.05  thf('88', plain,
% 36.85/37.05      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0)))
% 36.85/37.05         <= (~
% 36.85/37.05             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 36.85/37.05                = (k1_xboole_0))))),
% 36.85/37.05      inference('split', [status(esa)], ['7'])).
% 36.85/37.05  thf('89', plain,
% 36.85/37.05      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 36.85/37.05      inference('sat_resolution*', [status(thm)], ['8', '24', '31'])).
% 36.85/37.05  thf('90', plain,
% 36.85/37.05      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0))),
% 36.85/37.05      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 36.85/37.05  thf('91', plain, ($false),
% 36.85/37.05      inference('simplify_reflect-', [status(thm)], ['87', '90'])).
% 36.85/37.05  
% 36.85/37.05  % SZS output end Refutation
% 36.85/37.05  
% 36.85/37.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
