%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fbvOLpvmo9

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:42 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 117 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  695 (1163 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t107_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
      <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_xboole_1])).

thf('0',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t103_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k5_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t103_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X32 @ X33 ) @ ( k5_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ X31 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_xboole_0 @ X34 @ X35 )
      = ( k5_xboole_0 @ X34 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ~ ( r1_tarski @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k5_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t103_xboole_1])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('32',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_xboole_0 @ X34 @ X35 )
      = ( k5_xboole_0 @ X34 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ X31 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_xboole_0 @ X34 @ X35 )
      = ( k5_xboole_0 @ X34 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('48',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r1_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','21','22','45','46','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fbvOLpvmo9
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:32:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 400 iterations in 0.398s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.86  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(t107_xboole_1, conjecture,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.68/0.86       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.68/0.86         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.86        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.68/0.86          ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.68/0.86            ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t107_xboole_1])).
% 0.68/0.86  thf('0', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.86        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('1', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.68/0.86       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('split', [status(esa)], ['0'])).
% 0.68/0.86  thf(t103_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      (![X6 : $i, X7 : $i]:
% 0.68/0.86         (r1_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k5_xboole_0 @ X6 @ X7))),
% 0.68/0.86      inference('cnf', [status(esa)], [t103_xboole_1])).
% 0.68/0.86  thf(symmetry_r1_xboole_0, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.68/0.86  thf('3', plain,
% 0.68/0.86      (![X2 : $i, X3 : $i]:
% 0.68/0.86         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.68/0.86      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['2', '3'])).
% 0.68/0.86  thf(t83_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.86  thf('5', plain,
% 0.68/0.86      (![X23 : $i, X24 : $i]:
% 0.68/0.86         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 0.68/0.86      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.68/0.86  thf('6', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.86           = (k5_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.86  thf(t96_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      (![X32 : $i, X33 : $i]:
% 0.68/0.86         (r1_tarski @ (k4_xboole_0 @ X32 @ X33) @ (k5_xboole_0 @ X32 @ X33))),
% 0.68/0.86      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.68/0.86  thf('8', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ 
% 0.68/0.86          (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['6', '7'])).
% 0.68/0.86  thf(t91_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.68/0.86       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.68/0.86  thf('9', plain,
% 0.68/0.86      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.68/0.86         ((k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ X31)
% 0.68/0.86           = (k5_xboole_0 @ X29 @ (k5_xboole_0 @ X30 @ X31)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.68/0.86  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.86  thf('10', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.86  thf(t100_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      (![X4 : $i, X5 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ X4 @ X5)
% 0.68/0.86           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.86  thf('12', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.86           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['10', '11'])).
% 0.68/0.86  thf(t98_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.68/0.86  thf('13', plain,
% 0.68/0.86      (![X34 : $i, X35 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ X34 @ X35)
% 0.68/0.86           = (k5_xboole_0 @ X34 @ (k4_xboole_0 @ X35 @ X34)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.68/0.86  thf('14', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['8', '9', '12', '13'])).
% 0.68/0.86  thf('15', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('split', [status(esa)], ['0'])).
% 0.68/0.86  thf(t1_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.68/0.86       ( r1_tarski @ A @ C ) ))).
% 0.68/0.86  thf('16', plain,
% 0.68/0.86      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X11 @ X12)
% 0.68/0.86          | ~ (r1_tarski @ X12 @ X13)
% 0.68/0.86          | (r1_tarski @ X11 @ X13))),
% 0.68/0.86      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.68/0.86  thf('17', plain,
% 0.68/0.86      ((![X0 : $i]:
% 0.68/0.86          ((r1_tarski @ sk_A @ X0)
% 0.68/0.86           | ~ (r1_tarski @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)))
% 0.68/0.86         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.86  thf('18', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['14', '17'])).
% 0.68/0.86  thf('19', plain,
% 0.68/0.86      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.68/0.86        | ~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.86        | ~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('20', plain,
% 0.68/0.86      ((~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('split', [status(esa)], ['19'])).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.68/0.86       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['18', '20'])).
% 0.68/0.86  thf('22', plain,
% 0.68/0.86      (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.68/0.86       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 0.68/0.86       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('split', [status(esa)], ['19'])).
% 0.68/0.86  thf('23', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('split', [status(esa)], ['0'])).
% 0.68/0.86  thf('24', plain,
% 0.68/0.86      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.68/0.86        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('25', plain,
% 0.68/0.86      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('split', [status(esa)], ['24'])).
% 0.68/0.86  thf('26', plain,
% 0.68/0.86      (![X6 : $i, X7 : $i]:
% 0.68/0.86         (r1_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k5_xboole_0 @ X6 @ X7))),
% 0.68/0.86      inference('cnf', [status(esa)], [t103_xboole_1])).
% 0.68/0.86  thf('27', plain,
% 0.68/0.86      (![X23 : $i, X24 : $i]:
% 0.68/0.86         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 0.68/0.86      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.68/0.86  thf('28', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.68/0.86           = (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['26', '27'])).
% 0.68/0.86  thf(t49_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.68/0.86       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.68/0.86  thf('29', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.86         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.68/0.86           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.68/0.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.86  thf('30', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.68/0.86           = (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['28', '29'])).
% 0.68/0.86  thf('31', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.86         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.68/0.86           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.68/0.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.86  thf('32', plain,
% 0.68/0.86      (![X34 : $i, X35 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ X34 @ X35)
% 0.68/0.86           = (k5_xboole_0 @ X34 @ (k4_xboole_0 @ X35 @ X34)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.68/0.86  thf('33', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.68/0.86           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.68/0.86      inference('sup+', [status(thm)], ['31', '32'])).
% 0.68/0.86  thf('34', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.86           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['30', '33'])).
% 0.68/0.86  thf('35', plain,
% 0.68/0.86      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.68/0.86         ((k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ X31)
% 0.68/0.86           = (k5_xboole_0 @ X29 @ (k5_xboole_0 @ X30 @ X31)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.68/0.86  thf('36', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.86           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['10', '11'])).
% 0.68/0.86  thf('37', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.86           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.86      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.68/0.86  thf('38', plain,
% 0.68/0.86      (![X34 : $i, X35 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ X34 @ X35)
% 0.68/0.86           = (k5_xboole_0 @ X34 @ (k4_xboole_0 @ X35 @ X34)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.68/0.86  thf('39', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.86           = (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['37', '38'])).
% 0.68/0.86  thf(t73_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.68/0.86       ( r1_tarski @ A @ B ) ))).
% 0.68/0.86  thf('40', plain,
% 0.68/0.86      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.86         ((r1_tarski @ X20 @ X21)
% 0.68/0.86          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 0.68/0.86          | ~ (r1_xboole_0 @ X20 @ X22))),
% 0.68/0.86      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.68/0.86  thf('41', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.68/0.86          | ~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.86          | (r1_tarski @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['39', '40'])).
% 0.68/0.86  thf('42', plain,
% 0.68/0.86      ((((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))
% 0.68/0.86         | ~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.68/0.86         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['25', '41'])).
% 0.68/0.86  thf('43', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.68/0.86             ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['23', '42'])).
% 0.68/0.86  thf('44', plain,
% 0.68/0.86      ((~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('split', [status(esa)], ['19'])).
% 0.68/0.86  thf('45', plain,
% 0.68/0.86      (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.68/0.86       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 0.68/0.86       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['43', '44'])).
% 0.68/0.86  thf('46', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 0.68/0.86       ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('split', [status(esa)], ['24'])).
% 0.68/0.86  thf('47', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['2', '3'])).
% 0.68/0.86  thf('48', plain,
% 0.68/0.86      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('split', [status(esa)], ['0'])).
% 0.68/0.86  thf(t63_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.68/0.86       ( r1_xboole_0 @ A @ C ) ))).
% 0.68/0.86  thf('49', plain,
% 0.68/0.86      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.68/0.86         (~ (r1_tarski @ X17 @ X18)
% 0.68/0.86          | ~ (r1_xboole_0 @ X18 @ X19)
% 0.68/0.86          | (r1_xboole_0 @ X17 @ X19))),
% 0.68/0.86      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.68/0.86  thf('50', plain,
% 0.68/0.86      ((![X0 : $i]:
% 0.68/0.86          ((r1_xboole_0 @ sk_A @ X0)
% 0.68/0.86           | ~ (r1_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)))
% 0.68/0.86         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['48', '49'])).
% 0.68/0.86  thf('51', plain,
% 0.68/0.86      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('sup-', [status(thm)], ['47', '50'])).
% 0.68/0.86  thf('52', plain,
% 0.68/0.86      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.86         <= (~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.68/0.86      inference('split', [status(esa)], ['19'])).
% 0.68/0.86  thf('53', plain,
% 0.68/0.86      (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 0.68/0.86       ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['51', '52'])).
% 0.68/0.86  thf('54', plain, ($false),
% 0.68/0.86      inference('sat_resolution*', [status(thm)],
% 0.68/0.86                ['1', '21', '22', '45', '46', '53'])).
% 0.68/0.86  
% 0.68/0.86  % SZS output end Refutation
% 0.68/0.86  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
