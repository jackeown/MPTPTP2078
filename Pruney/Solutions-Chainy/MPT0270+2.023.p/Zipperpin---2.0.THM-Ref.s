%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UGyIkMAS4O

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:14 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 202 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   21
%              Number of atoms          :  676 (1889 expanded)
%              Number of equality atoms :   69 ( 202 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
        | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('25',plain,
    ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('35',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 != X52 )
      | ~ ( r2_hidden @ X50 @ ( k4_xboole_0 @ X51 @ ( k1_tarski @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('36',plain,(
    ! [X51: $i,X52: $i] :
      ~ ( r2_hidden @ X52 @ ( k4_xboole_0 @ X51 @ ( k1_tarski @ X52 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('41',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('43',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('53',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','38','52'])).

thf('54',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['40','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UGyIkMAS4O
% 0.14/0.37  % Computer   : n013.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:25:55 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 380 iterations in 0.142s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(t67_zfmisc_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.62       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i]:
% 0.40/0.62        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.62          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.40/0.62        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.40/0.62       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (((r2_hidden @ sk_A @ sk_B_1)
% 0.40/0.62        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.40/0.62      inference('split', [status(esa)], ['3'])).
% 0.40/0.62  thf(t7_xboole_0, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf(t48_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.40/0.62           = (k3_xboole_0 @ X12 @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.62          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.62          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.40/0.62           = (k3_xboole_0 @ X12 @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.40/0.62          (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.40/0.62          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.62  thf('13', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.40/0.62          (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) = (k1_tarski @ sk_A)))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.40/0.62           = (k3_xboole_0 @ X12 @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.62          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.40/0.62             (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.62          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.40/0.62          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.40/0.62             (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.62  thf(t4_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.40/0.62          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.62          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      ((![X0 : $i]:
% 0.40/0.62          (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.40/0.62           | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.40/0.62                (k1_tarski @ sk_A))))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '21'])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.62          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf(t79_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.40/0.62      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (((r1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.40/0.62         (k1_tarski @ sk_A)))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('sup+', [status(thm)], ['23', '24'])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      ((![X0 : $i]:
% 0.40/0.62          ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['22', '25'])).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['5', '26'])).
% 0.40/0.62  thf(t100_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (![X10 : $i, X11 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X10 @ X11)
% 0.40/0.62           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      ((((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.40/0.62          = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.40/0.62  thf(commutativity_k5_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.62  thf(t5_boole, axiom,
% 0.40/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.62  thf('32', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.40/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.62  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('34', plain,
% 0.40/0.62      ((((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1)))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.40/0.62  thf(t64_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.40/0.62       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.40/0.62         (((X50) != (X52))
% 0.40/0.62          | ~ (r2_hidden @ X50 @ (k4_xboole_0 @ X51 @ (k1_tarski @ X52))))),
% 0.40/0.62      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.40/0.62  thf('36', plain,
% 0.40/0.62      (![X51 : $i, X52 : $i]:
% 0.40/0.62         ~ (r2_hidden @ X52 @ (k4_xboole_0 @ X51 @ (k1_tarski @ X52)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['35'])).
% 0.40/0.62  thf('37', plain,
% 0.40/0.62      ((~ (r2_hidden @ sk_A @ sk_B_1))
% 0.40/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '36'])).
% 0.40/0.62  thf('38', plain,
% 0.40/0.62      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.40/0.62       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['4', '37'])).
% 0.40/0.62  thf('39', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['2', '38'])).
% 0.40/0.62  thf('40', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.40/0.62      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.40/0.62  thf(l27_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      (![X48 : $i, X49 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.40/0.62      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.40/0.62  thf('42', plain,
% 0.40/0.62      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.62  thf('43', plain,
% 0.40/0.62      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.40/0.62          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf('44', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.40/0.62  thf('45', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_hidden @ X1 @ X0)
% 0.40/0.62          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['41', '44'])).
% 0.40/0.62  thf('46', plain,
% 0.40/0.62      (![X10 : $i, X11 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X10 @ X11)
% 0.40/0.62           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.62  thf('47', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.40/0.62            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 0.40/0.62          | (r2_hidden @ X1 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['45', '46'])).
% 0.40/0.62  thf('48', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.62  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('50', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.40/0.62          | (r2_hidden @ X1 @ X0))),
% 0.40/0.62      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.40/0.62  thf('51', plain,
% 0.40/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.62      inference('split', [status(esa)], ['3'])).
% 0.40/0.62  thf('52', plain,
% 0.40/0.62      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.40/0.62       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('split', [status(esa)], ['3'])).
% 0.40/0.62  thf('53', plain,
% 0.40/0.62      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['2', '38', '52'])).
% 0.40/0.62  thf('54', plain,
% 0.40/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.40/0.62      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 0.40/0.62  thf('55', plain,
% 0.40/0.62      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.40/0.62        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['50', '54'])).
% 0.40/0.62  thf('56', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.40/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.40/0.62  thf('57', plain, ($false), inference('demod', [status(thm)], ['40', '56'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
