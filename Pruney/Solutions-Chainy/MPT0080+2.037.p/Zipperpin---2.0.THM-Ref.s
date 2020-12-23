%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G0bLzg6F5u

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:08 EST 2020

% Result     : Theorem 3.41s
% Output     : Refutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 215 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   26
%              Number of atoms          :  960 (1758 expanded)
%              Number of equality atoms :   71 ( 130 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','33'])).

thf('35',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('41',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 )
      | ( r1_xboole_0 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','72'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('76',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','80'])).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','28'])).

thf('85',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('91',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('93',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('95',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G0bLzg6F5u
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.41/3.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.41/3.59  % Solved by: fo/fo7.sh
% 3.41/3.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.41/3.59  % done 3972 iterations in 3.140s
% 3.41/3.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.41/3.59  % SZS output start Refutation
% 3.41/3.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.41/3.59  thf(sk_A_type, type, sk_A: $i).
% 3.41/3.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.41/3.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.41/3.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.41/3.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.41/3.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.41/3.59  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.41/3.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.41/3.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.41/3.59  thf(sk_B_type, type, sk_B: $i).
% 3.41/3.59  thf(t73_xboole_1, conjecture,
% 3.41/3.59    (![A:$i,B:$i,C:$i]:
% 3.41/3.59     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 3.41/3.59       ( r1_tarski @ A @ B ) ))).
% 3.41/3.59  thf(zf_stmt_0, negated_conjecture,
% 3.41/3.59    (~( ![A:$i,B:$i,C:$i]:
% 3.41/3.59        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 3.41/3.59            ( r1_xboole_0 @ A @ C ) ) =>
% 3.41/3.59          ( r1_tarski @ A @ B ) ) )),
% 3.41/3.59    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 3.41/3.59  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 3.41/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.59  thf(t3_xboole_0, axiom,
% 3.41/3.59    (![A:$i,B:$i]:
% 3.41/3.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.41/3.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.41/3.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.41/3.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.41/3.59  thf('1', plain,
% 3.41/3.59      (![X7 : $i, X8 : $i]:
% 3.41/3.59         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 3.41/3.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.41/3.59  thf(t41_xboole_1, axiom,
% 3.41/3.59    (![A:$i,B:$i,C:$i]:
% 3.41/3.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.41/3.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.41/3.59  thf('2', plain,
% 3.41/3.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.41/3.59           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.41/3.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.41/3.59  thf(t39_xboole_1, axiom,
% 3.41/3.59    (![A:$i,B:$i]:
% 3.41/3.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.41/3.59  thf('3', plain,
% 3.41/3.59      (![X15 : $i, X16 : $i]:
% 3.41/3.59         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 3.41/3.59           = (k2_xboole_0 @ X15 @ X16))),
% 3.41/3.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.41/3.59  thf('4', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.41/3.59           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 3.41/3.59      inference('sup+', [status(thm)], ['2', '3'])).
% 3.41/3.59  thf(t48_xboole_1, axiom,
% 3.41/3.59    (![A:$i,B:$i]:
% 3.41/3.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.41/3.59  thf('5', plain,
% 3.41/3.59      (![X25 : $i, X26 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 3.41/3.59           = (k3_xboole_0 @ X25 @ X26))),
% 3.41/3.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.41/3.59  thf('6', plain,
% 3.41/3.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.41/3.59           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.41/3.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.41/3.59  thf('7', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 3.41/3.59           = (k4_xboole_0 @ X2 @ 
% 3.41/3.59              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 3.41/3.59      inference('sup+', [status(thm)], ['5', '6'])).
% 3.41/3.59  thf('8', plain,
% 3.41/3.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.41/3.59           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.41/3.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.41/3.59  thf('9', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 3.41/3.59           = (k4_xboole_0 @ X2 @ 
% 3.41/3.59              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 3.41/3.59      inference('demod', [status(thm)], ['7', '8'])).
% 3.41/3.59  thf('10', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]:
% 3.41/3.59         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 3.41/3.59           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.41/3.59      inference('sup+', [status(thm)], ['4', '9'])).
% 3.41/3.59  thf('11', plain,
% 3.41/3.59      (![X15 : $i, X16 : $i]:
% 3.41/3.59         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 3.41/3.59           = (k2_xboole_0 @ X15 @ X16))),
% 3.41/3.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.41/3.59  thf('12', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]:
% 3.41/3.59         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 3.41/3.59           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.41/3.59      inference('demod', [status(thm)], ['10', '11'])).
% 3.41/3.59  thf(t3_boole, axiom,
% 3.41/3.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.41/3.59  thf('13', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.41/3.59      inference('cnf', [status(esa)], [t3_boole])).
% 3.41/3.59  thf('14', plain,
% 3.41/3.59      (![X25 : $i, X26 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 3.41/3.59           = (k3_xboole_0 @ X25 @ X26))),
% 3.41/3.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.41/3.59  thf('15', plain,
% 3.41/3.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.41/3.59      inference('sup+', [status(thm)], ['13', '14'])).
% 3.41/3.59  thf('16', plain,
% 3.41/3.59      (![X7 : $i, X8 : $i]:
% 3.41/3.59         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 3.41/3.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.41/3.59  thf('17', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 3.41/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.59  thf(d7_xboole_0, axiom,
% 3.41/3.59    (![A:$i,B:$i]:
% 3.41/3.59     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.41/3.59       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.41/3.59  thf('18', plain,
% 3.41/3.59      (![X2 : $i, X3 : $i]:
% 3.41/3.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.41/3.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.41/3.59  thf('19', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 3.41/3.59      inference('sup-', [status(thm)], ['17', '18'])).
% 3.41/3.59  thf(t4_xboole_0, axiom,
% 3.41/3.59    (![A:$i,B:$i]:
% 3.41/3.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 3.41/3.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.41/3.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.41/3.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 3.41/3.59  thf('20', plain,
% 3.41/3.59      (![X11 : $i, X13 : $i, X14 : $i]:
% 3.41/3.59         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 3.41/3.59          | ~ (r1_xboole_0 @ X11 @ X14))),
% 3.41/3.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.41/3.59  thf('21', plain,
% 3.41/3.59      (![X0 : $i]:
% 3.41/3.59         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_A @ sk_C_2))),
% 3.41/3.59      inference('sup-', [status(thm)], ['19', '20'])).
% 3.41/3.59  thf('22', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 3.41/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.59  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.41/3.59      inference('demod', [status(thm)], ['21', '22'])).
% 3.41/3.59  thf('24', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.41/3.59      inference('sup-', [status(thm)], ['16', '23'])).
% 3.41/3.59  thf(symmetry_r1_xboole_0, axiom,
% 3.41/3.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 3.41/3.59  thf('25', plain,
% 3.41/3.59      (![X5 : $i, X6 : $i]:
% 3.41/3.59         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.41/3.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.41/3.59  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.41/3.59      inference('sup-', [status(thm)], ['24', '25'])).
% 3.41/3.59  thf('27', plain,
% 3.41/3.59      (![X2 : $i, X3 : $i]:
% 3.41/3.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.41/3.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.41/3.59  thf('28', plain,
% 3.41/3.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.41/3.59      inference('sup-', [status(thm)], ['26', '27'])).
% 3.41/3.59  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.41/3.59      inference('demod', [status(thm)], ['15', '28'])).
% 3.41/3.59  thf('30', plain,
% 3.41/3.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.41/3.59           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.41/3.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.41/3.59  thf('31', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]:
% 3.41/3.59         ((k1_xboole_0)
% 3.41/3.59           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.41/3.59      inference('sup+', [status(thm)], ['29', '30'])).
% 3.41/3.59  thf('32', plain,
% 3.41/3.59      (![X15 : $i, X16 : $i]:
% 3.41/3.59         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 3.41/3.59           = (k2_xboole_0 @ X15 @ X16))),
% 3.41/3.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.41/3.59  thf('33', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]:
% 3.41/3.59         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.41/3.59      inference('demod', [status(thm)], ['31', '32'])).
% 3.41/3.59  thf('34', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]:
% 3.41/3.59         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 3.41/3.59      inference('demod', [status(thm)], ['12', '33'])).
% 3.41/3.59  thf('35', plain,
% 3.41/3.59      (![X2 : $i, X4 : $i]:
% 3.41/3.59         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.41/3.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.41/3.59  thf('36', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]:
% 3.41/3.59         (((k1_xboole_0) != (k1_xboole_0))
% 3.41/3.59          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.41/3.59      inference('sup-', [status(thm)], ['34', '35'])).
% 3.41/3.59  thf('37', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 3.41/3.59      inference('simplify', [status(thm)], ['36'])).
% 3.41/3.59  thf('38', plain,
% 3.41/3.59      (![X5 : $i, X6 : $i]:
% 3.41/3.59         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.41/3.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.41/3.59  thf('39', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 3.41/3.59      inference('sup-', [status(thm)], ['37', '38'])).
% 3.41/3.59  thf('40', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 3.41/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.59  thf(t63_xboole_1, axiom,
% 3.41/3.59    (![A:$i,B:$i,C:$i]:
% 3.41/3.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 3.41/3.59       ( r1_xboole_0 @ A @ C ) ))).
% 3.41/3.59  thf('41', plain,
% 3.41/3.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.41/3.59         (~ (r1_tarski @ X27 @ X28)
% 3.41/3.59          | ~ (r1_xboole_0 @ X28 @ X29)
% 3.41/3.59          | (r1_xboole_0 @ X27 @ X29))),
% 3.41/3.59      inference('cnf', [status(esa)], [t63_xboole_1])).
% 3.41/3.59  thf('42', plain,
% 3.41/3.59      (![X0 : $i]:
% 3.41/3.59         ((r1_xboole_0 @ sk_A @ X0)
% 3.41/3.59          | ~ (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0))),
% 3.41/3.59      inference('sup-', [status(thm)], ['40', '41'])).
% 3.41/3.59  thf('43', plain,
% 3.41/3.59      (![X0 : $i]:
% 3.41/3.59         (r1_xboole_0 @ sk_A @ 
% 3.41/3.59          (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 3.41/3.59      inference('sup-', [status(thm)], ['39', '42'])).
% 3.41/3.59  thf('44', plain,
% 3.41/3.59      (![X7 : $i, X8 : $i]:
% 3.41/3.59         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X8))),
% 3.41/3.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.41/3.59  thf('45', plain,
% 3.41/3.59      (![X25 : $i, X26 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 3.41/3.59           = (k3_xboole_0 @ X25 @ X26))),
% 3.41/3.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.41/3.59  thf('46', plain,
% 3.41/3.59      (![X25 : $i, X26 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 3.41/3.59           = (k3_xboole_0 @ X25 @ X26))),
% 3.41/3.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.41/3.59  thf('47', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.41/3.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.41/3.59      inference('sup+', [status(thm)], ['45', '46'])).
% 3.41/3.59  thf(t47_xboole_1, axiom,
% 3.41/3.59    (![A:$i,B:$i]:
% 3.41/3.59     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.41/3.59  thf('48', plain,
% 3.41/3.59      (![X23 : $i, X24 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 3.41/3.59           = (k4_xboole_0 @ X23 @ X24))),
% 3.41/3.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 3.41/3.59  thf('49', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]:
% 3.41/3.59         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 3.41/3.59           = (k4_xboole_0 @ X1 @ X0))),
% 3.41/3.59      inference('sup+', [status(thm)], ['47', '48'])).
% 3.41/3.59  thf('50', plain,
% 3.41/3.59      (![X11 : $i, X13 : $i, X14 : $i]:
% 3.41/3.59         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 3.41/3.59          | ~ (r1_xboole_0 @ X11 @ X14))),
% 3.41/3.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.41/3.59  thf('51', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.41/3.59          | ~ (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.41/3.59      inference('sup-', [status(thm)], ['49', '50'])).
% 3.41/3.59  thf('52', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.41/3.59          | ~ (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.41/3.59      inference('sup-', [status(thm)], ['44', '51'])).
% 3.41/3.59  thf('53', plain,
% 3.41/3.59      (![X0 : $i]:
% 3.41/3.59         (r1_xboole_0 @ X0 @ 
% 3.41/3.59          (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 3.41/3.59      inference('sup-', [status(thm)], ['43', '52'])).
% 3.41/3.59  thf(commutativity_k2_xboole_0, axiom,
% 3.41/3.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.41/3.59  thf('54', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.41/3.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.41/3.59  thf('55', plain,
% 3.41/3.59      (![X23 : $i, X24 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 3.41/3.59           = (k4_xboole_0 @ X23 @ X24))),
% 3.41/3.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 3.41/3.59  thf('56', plain,
% 3.41/3.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.41/3.59           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.41/3.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.41/3.59  thf('57', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.41/3.59           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 3.41/3.59      inference('sup+', [status(thm)], ['55', '56'])).
% 3.41/3.59  thf('58', plain,
% 3.41/3.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.41/3.59           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.41/3.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.41/3.59  thf('59', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 3.41/3.59           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 3.41/3.59      inference('demod', [status(thm)], ['57', '58'])).
% 3.41/3.59  thf('60', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.41/3.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.41/3.59  thf(t40_xboole_1, axiom,
% 3.41/3.59    (![A:$i,B:$i]:
% 3.41/3.59     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.41/3.59  thf('61', plain,
% 3.41/3.59      (![X18 : $i, X19 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 3.41/3.59           = (k4_xboole_0 @ X18 @ X19))),
% 3.41/3.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 3.41/3.59  thf('62', plain,
% 3.41/3.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.41/3.59           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.41/3.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.41/3.59  thf('63', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.41/3.59           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 3.41/3.59      inference('sup+', [status(thm)], ['61', '62'])).
% 3.41/3.59  thf('64', plain,
% 3.41/3.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.41/3.59           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.41/3.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.41/3.59  thf('65', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 3.41/3.59           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 3.41/3.59      inference('demod', [status(thm)], ['63', '64'])).
% 3.41/3.59  thf('66', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.41/3.59          | ~ (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.41/3.59      inference('sup-', [status(thm)], ['49', '50'])).
% 3.41/3.59  thf('67', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.41/3.59         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.41/3.59          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 3.41/3.59               (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))))),
% 3.41/3.59      inference('sup-', [status(thm)], ['65', '66'])).
% 3.41/3.59  thf('68', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 3.41/3.59           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 3.41/3.59      inference('demod', [status(thm)], ['63', '64'])).
% 3.41/3.59  thf('69', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.41/3.59         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.41/3.59          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 3.41/3.59               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 3.41/3.59      inference('demod', [status(thm)], ['67', '68'])).
% 3.41/3.59  thf('70', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.41/3.59         (~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ 
% 3.41/3.59             (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.41/3.59          | ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))))),
% 3.41/3.59      inference('sup-', [status(thm)], ['60', '69'])).
% 3.41/3.59  thf('71', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.41/3.59         (~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ 
% 3.41/3.59             (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.41/3.59          | ~ (r2_hidden @ X3 @ 
% 3.41/3.59               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))))),
% 3.41/3.59      inference('sup-', [status(thm)], ['59', '70'])).
% 3.41/3.59  thf('72', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.41/3.59         (~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 3.41/3.59             (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.41/3.59          | ~ (r2_hidden @ X3 @ 
% 3.41/3.59               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))))),
% 3.41/3.59      inference('sup-', [status(thm)], ['54', '71'])).
% 3.41/3.59  thf('73', plain,
% 3.41/3.59      (![X0 : $i]:
% 3.41/3.59         ~ (r2_hidden @ X0 @ 
% 3.41/3.59            (k4_xboole_0 @ sk_A @ 
% 3.41/3.59             (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C_2))))),
% 3.41/3.59      inference('sup-', [status(thm)], ['53', '72'])).
% 3.41/3.59  thf('74', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 3.41/3.59      inference('sup-', [status(thm)], ['17', '18'])).
% 3.41/3.59  thf('75', plain,
% 3.41/3.59      (![X18 : $i, X19 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 3.41/3.59           = (k4_xboole_0 @ X18 @ X19))),
% 3.41/3.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 3.41/3.59  thf('76', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.41/3.59      inference('cnf', [status(esa)], [t3_boole])).
% 3.41/3.59  thf('77', plain,
% 3.41/3.59      (![X0 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 3.41/3.59      inference('sup+', [status(thm)], ['75', '76'])).
% 3.41/3.59  thf('78', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.41/3.59      inference('cnf', [status(esa)], [t3_boole])).
% 3.41/3.59  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.41/3.59      inference('sup+', [status(thm)], ['77', '78'])).
% 3.41/3.59  thf('80', plain,
% 3.41/3.59      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 3.41/3.59      inference('demod', [status(thm)], ['73', '74', '79'])).
% 3.41/3.59  thf('81', plain,
% 3.41/3.59      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 3.41/3.59      inference('sup-', [status(thm)], ['1', '80'])).
% 3.41/3.59  thf('82', plain,
% 3.41/3.59      (![X2 : $i, X3 : $i]:
% 3.41/3.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.41/3.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.41/3.59  thf('83', plain,
% 3.41/3.59      (![X0 : $i]:
% 3.41/3.59         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) = (k1_xboole_0))),
% 3.41/3.59      inference('sup-', [status(thm)], ['81', '82'])).
% 3.41/3.59  thf('84', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.41/3.59      inference('demod', [status(thm)], ['15', '28'])).
% 3.41/3.59  thf('85', plain,
% 3.41/3.59      (![X25 : $i, X26 : $i]:
% 3.41/3.59         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 3.41/3.59           = (k3_xboole_0 @ X25 @ X26))),
% 3.41/3.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.41/3.59  thf('86', plain,
% 3.41/3.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 3.41/3.59      inference('sup+', [status(thm)], ['84', '85'])).
% 3.41/3.59  thf('87', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.41/3.59      inference('cnf', [status(esa)], [t3_boole])).
% 3.41/3.59  thf('88', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 3.41/3.59      inference('demod', [status(thm)], ['86', '87'])).
% 3.41/3.59  thf('89', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 3.41/3.59      inference('sup+', [status(thm)], ['83', '88'])).
% 3.41/3.59  thf('90', plain,
% 3.41/3.59      (![X15 : $i, X16 : $i]:
% 3.41/3.59         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 3.41/3.59           = (k2_xboole_0 @ X15 @ X16))),
% 3.41/3.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.41/3.59  thf('91', plain,
% 3.41/3.59      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 3.41/3.59      inference('sup+', [status(thm)], ['89', '90'])).
% 3.41/3.59  thf('92', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.41/3.59      inference('sup+', [status(thm)], ['77', '78'])).
% 3.41/3.59  thf('93', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 3.41/3.59      inference('demod', [status(thm)], ['91', '92'])).
% 3.41/3.59  thf('94', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.41/3.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.41/3.59  thf(t7_xboole_1, axiom,
% 3.41/3.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.41/3.59  thf('95', plain,
% 3.41/3.59      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 3.41/3.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.41/3.59  thf('96', plain,
% 3.41/3.59      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.41/3.59      inference('sup+', [status(thm)], ['94', '95'])).
% 3.41/3.59  thf('97', plain, ((r1_tarski @ sk_A @ sk_B)),
% 3.41/3.59      inference('sup+', [status(thm)], ['93', '96'])).
% 3.41/3.59  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 3.41/3.59  
% 3.41/3.59  % SZS output end Refutation
% 3.41/3.59  
% 3.41/3.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
