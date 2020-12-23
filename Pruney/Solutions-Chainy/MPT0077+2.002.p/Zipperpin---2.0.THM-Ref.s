%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2x28VoyHKK

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:49 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 480 expanded)
%              Number of leaves         :   28 ( 148 expanded)
%              Depth                    :   17
%              Number of atoms          : 1104 (4537 expanded)
%              Number of equality atoms :   70 ( 186 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ X34 @ ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_xboole_0 @ X32 @ X33 )
      | ( r1_xboole_0 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','23'])).

thf('25',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('31',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','23','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('43',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('45',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','23','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X24 @ X26 ) @ X25 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B_1 ) @ sk_A )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B_1 ) @ sk_A )
      = ( k2_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('70',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('71',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('72',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('75',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('76',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','79'])).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','82'])).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('86',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','82'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('96',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('97',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('106',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('107',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','23','44'])).

thf('108',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('110',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ X34 @ ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_xboole_0 @ X32 @ X33 )
      | ( r1_xboole_0 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('118',plain,(
    r1_xboole_0 @ sk_B_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('120',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['104','105','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['56','122'])).

thf('124',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['40','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['25','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2x28VoyHKK
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:41:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.55/2.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.55/2.76  % Solved by: fo/fo7.sh
% 2.55/2.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.55/2.76  % done 3717 iterations in 2.304s
% 2.55/2.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.55/2.76  % SZS output start Refutation
% 2.55/2.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.55/2.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.55/2.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.55/2.76  thf(sk_A_type, type, sk_A: $i).
% 2.55/2.76  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.55/2.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.55/2.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.55/2.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.55/2.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.55/2.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.55/2.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.55/2.76  thf(sk_B_type, type, sk_B: $i > $i).
% 2.55/2.76  thf(t70_xboole_1, conjecture,
% 2.55/2.76    (![A:$i,B:$i,C:$i]:
% 2.55/2.76     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.55/2.76            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.55/2.76       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.55/2.76            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.55/2.76  thf(zf_stmt_0, negated_conjecture,
% 2.55/2.76    (~( ![A:$i,B:$i,C:$i]:
% 2.55/2.76        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.55/2.76               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.55/2.76          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.55/2.76               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 2.55/2.76    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 2.55/2.76  thf('0', plain,
% 2.55/2.76      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 2.55/2.76        | ~ (r1_xboole_0 @ sk_A @ sk_B_1)
% 2.55/2.76        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 2.55/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.76  thf('1', plain,
% 2.55/2.76      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 2.55/2.76         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 2.55/2.76      inference('split', [status(esa)], ['0'])).
% 2.55/2.76  thf('2', plain,
% 2.55/2.76      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))) | 
% 2.55/2.76       ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B_1))),
% 2.55/2.76      inference('split', [status(esa)], ['0'])).
% 2.55/2.76  thf('3', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 2.55/2.76        | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 2.55/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.76  thf('4', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 2.55/2.76         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 2.55/2.76      inference('split', [status(esa)], ['3'])).
% 2.55/2.76  thf(symmetry_r1_xboole_0, axiom,
% 2.55/2.76    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.55/2.76  thf('5', plain,
% 2.55/2.76      (![X10 : $i, X11 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.55/2.76      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.55/2.76  thf('6', plain,
% 2.55/2.76      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 2.55/2.76         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 2.55/2.76      inference('sup-', [status(thm)], ['4', '5'])).
% 2.55/2.76  thf(t7_xboole_1, axiom,
% 2.55/2.76    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.55/2.76  thf('7', plain,
% 2.55/2.76      (![X34 : $i, X35 : $i]: (r1_tarski @ X34 @ (k2_xboole_0 @ X34 @ X35))),
% 2.55/2.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.55/2.76  thf(t63_xboole_1, axiom,
% 2.55/2.76    (![A:$i,B:$i,C:$i]:
% 2.55/2.76     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 2.55/2.76       ( r1_xboole_0 @ A @ C ) ))).
% 2.55/2.76  thf('8', plain,
% 2.55/2.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.55/2.76         (~ (r1_tarski @ X31 @ X32)
% 2.55/2.76          | ~ (r1_xboole_0 @ X32 @ X33)
% 2.55/2.76          | (r1_xboole_0 @ X31 @ X33))),
% 2.55/2.76      inference('cnf', [status(esa)], [t63_xboole_1])).
% 2.55/2.76  thf('9', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X1 @ X2)
% 2.55/2.76          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.55/2.76      inference('sup-', [status(thm)], ['7', '8'])).
% 2.55/2.76  thf('10', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_B_1 @ sk_A))
% 2.55/2.76         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 2.55/2.76      inference('sup-', [status(thm)], ['6', '9'])).
% 2.55/2.76  thf('11', plain,
% 2.55/2.76      (![X10 : $i, X11 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.55/2.76      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.55/2.76  thf('12', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_B_1))
% 2.55/2.76         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 2.55/2.76      inference('sup-', [status(thm)], ['10', '11'])).
% 2.55/2.76  thf('13', plain,
% 2.55/2.76      ((~ (r1_xboole_0 @ sk_A @ sk_B_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 2.55/2.76      inference('split', [status(esa)], ['0'])).
% 2.55/2.76  thf('14', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 2.55/2.76       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 2.55/2.76      inference('sup-', [status(thm)], ['12', '13'])).
% 2.55/2.76  thf('15', plain,
% 2.55/2.76      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 2.55/2.76         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 2.55/2.76      inference('sup-', [status(thm)], ['4', '5'])).
% 2.55/2.76  thf(commutativity_k2_xboole_0, axiom,
% 2.55/2.76    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.55/2.76  thf('16', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.76  thf('17', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X1 @ X2)
% 2.55/2.76          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.55/2.76      inference('sup-', [status(thm)], ['7', '8'])).
% 2.55/2.76  thf('18', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.76         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.55/2.76          | (r1_xboole_0 @ X0 @ X2))),
% 2.55/2.76      inference('sup-', [status(thm)], ['16', '17'])).
% 2.55/2.76  thf('19', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_C_1 @ sk_A))
% 2.55/2.76         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 2.55/2.76      inference('sup-', [status(thm)], ['15', '18'])).
% 2.55/2.76  thf('20', plain,
% 2.55/2.76      (![X10 : $i, X11 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.55/2.76      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.55/2.76  thf('21', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 2.55/2.76         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 2.55/2.76      inference('sup-', [status(thm)], ['19', '20'])).
% 2.55/2.76  thf('22', plain,
% 2.55/2.76      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 2.55/2.76      inference('split', [status(esa)], ['0'])).
% 2.55/2.76  thf('23', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 2.55/2.76       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 2.55/2.76      inference('sup-', [status(thm)], ['21', '22'])).
% 2.55/2.76  thf('24', plain,
% 2.55/2.76      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 2.55/2.76      inference('sat_resolution*', [status(thm)], ['2', '14', '23'])).
% 2.55/2.76  thf('25', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.55/2.76      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 2.55/2.76  thf('26', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 2.55/2.76        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 2.55/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.76  thf('27', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 2.55/2.76      inference('split', [status(esa)], ['26'])).
% 2.55/2.76  thf('28', plain,
% 2.55/2.76      (![X10 : $i, X11 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.55/2.76      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.55/2.76  thf('29', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_C_1 @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 2.55/2.76      inference('sup-', [status(thm)], ['27', '28'])).
% 2.55/2.76  thf('30', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 2.55/2.76       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 2.55/2.76      inference('split', [status(esa)], ['26'])).
% 2.55/2.76  thf('31', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 2.55/2.76      inference('sat_resolution*', [status(thm)], ['2', '14', '23', '30'])).
% 2.55/2.76  thf('32', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 2.55/2.76      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 2.55/2.76  thf(t7_xboole_0, axiom,
% 2.55/2.76    (![A:$i]:
% 2.55/2.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.55/2.76          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.55/2.76  thf('33', plain,
% 2.55/2.76      (![X16 : $i]:
% 2.55/2.76         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 2.55/2.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.55/2.76  thf(t4_xboole_0, axiom,
% 2.55/2.76    (![A:$i,B:$i]:
% 2.55/2.76     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.55/2.76            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.55/2.76       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.55/2.76            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.55/2.76  thf('34', plain,
% 2.55/2.76      (![X12 : $i, X14 : $i, X15 : $i]:
% 2.55/2.76         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 2.55/2.76          | ~ (r1_xboole_0 @ X12 @ X15))),
% 2.55/2.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.55/2.76  thf('35', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['33', '34'])).
% 2.55/2.76  thf('36', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['32', '35'])).
% 2.55/2.76  thf(t47_xboole_1, axiom,
% 2.55/2.76    (![A:$i,B:$i]:
% 2.55/2.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.55/2.76  thf('37', plain,
% 2.55/2.76      (![X27 : $i, X28 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28))
% 2.55/2.76           = (k4_xboole_0 @ X27 @ X28))),
% 2.55/2.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.55/2.76  thf('38', plain,
% 2.55/2.76      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 2.55/2.76      inference('sup+', [status(thm)], ['36', '37'])).
% 2.55/2.76  thf(t3_boole, axiom,
% 2.55/2.76    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.55/2.76  thf('39', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 2.55/2.76      inference('cnf', [status(esa)], [t3_boole])).
% 2.55/2.76  thf('40', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 2.55/2.76      inference('demod', [status(thm)], ['38', '39'])).
% 2.55/2.76  thf('41', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 2.55/2.76      inference('split', [status(esa)], ['3'])).
% 2.55/2.76  thf('42', plain,
% 2.55/2.76      (![X10 : $i, X11 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.55/2.76      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.55/2.76  thf('43', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_B_1 @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 2.55/2.76      inference('sup-', [status(thm)], ['41', '42'])).
% 2.55/2.76  thf('44', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 2.55/2.76       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 2.55/2.76      inference('split', [status(esa)], ['3'])).
% 2.55/2.76  thf('45', plain, (((r1_xboole_0 @ sk_A @ sk_B_1))),
% 2.55/2.76      inference('sat_resolution*', [status(thm)], ['2', '14', '23', '44'])).
% 2.55/2.76  thf('46', plain, ((r1_xboole_0 @ sk_B_1 @ sk_A)),
% 2.55/2.76      inference('simpl_trail', [status(thm)], ['43', '45'])).
% 2.55/2.76  thf('47', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['33', '34'])).
% 2.55/2.76  thf('48', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['46', '47'])).
% 2.55/2.76  thf('49', plain,
% 2.55/2.76      (![X27 : $i, X28 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28))
% 2.55/2.76           = (k4_xboole_0 @ X27 @ X28))),
% 2.55/2.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.55/2.76  thf('50', plain,
% 2.55/2.76      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 2.55/2.76      inference('sup+', [status(thm)], ['48', '49'])).
% 2.55/2.76  thf('51', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 2.55/2.76      inference('cnf', [status(esa)], [t3_boole])).
% 2.55/2.76  thf('52', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 2.55/2.76      inference('demod', [status(thm)], ['50', '51'])).
% 2.55/2.76  thf(t42_xboole_1, axiom,
% 2.55/2.76    (![A:$i,B:$i,C:$i]:
% 2.55/2.76     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.55/2.76       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.55/2.76  thf('53', plain,
% 2.55/2.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ (k2_xboole_0 @ X24 @ X26) @ X25)
% 2.55/2.76           = (k2_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ 
% 2.55/2.76              (k4_xboole_0 @ X26 @ X25)))),
% 2.55/2.76      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.55/2.76  thf('54', plain,
% 2.55/2.76      (![X0 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B_1) @ sk_A)
% 2.55/2.76           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B_1))),
% 2.55/2.76      inference('sup+', [status(thm)], ['52', '53'])).
% 2.55/2.76  thf('55', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.76  thf('56', plain,
% 2.55/2.76      (![X0 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B_1) @ sk_A)
% 2.55/2.76           = (k2_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_A)))),
% 2.55/2.76      inference('demod', [status(thm)], ['54', '55'])).
% 2.55/2.76  thf(t41_xboole_1, axiom,
% 2.55/2.76    (![A:$i,B:$i,C:$i]:
% 2.55/2.76     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.55/2.76       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.55/2.76  thf('57', plain,
% 2.55/2.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 2.55/2.76           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 2.55/2.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.55/2.76  thf(t39_xboole_1, axiom,
% 2.55/2.76    (![A:$i,B:$i]:
% 2.55/2.76     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.55/2.76  thf('58', plain,
% 2.55/2.76      (![X18 : $i, X19 : $i]:
% 2.55/2.76         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 2.55/2.76           = (k2_xboole_0 @ X18 @ X19))),
% 2.55/2.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.55/2.76  thf('59', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.76         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.55/2.76           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 2.55/2.76      inference('sup+', [status(thm)], ['57', '58'])).
% 2.55/2.76  thf('60', plain,
% 2.55/2.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 2.55/2.76           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 2.55/2.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.55/2.76  thf(t48_xboole_1, axiom,
% 2.55/2.76    (![A:$i,B:$i]:
% 2.55/2.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.55/2.76  thf('61', plain,
% 2.55/2.76      (![X29 : $i, X30 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 2.55/2.76           = (k3_xboole_0 @ X29 @ X30))),
% 2.55/2.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.55/2.76  thf('62', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X2 @ 
% 2.55/2.76           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 2.55/2.76           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.55/2.76      inference('sup+', [status(thm)], ['60', '61'])).
% 2.55/2.76  thf('63', plain,
% 2.55/2.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 2.55/2.76           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 2.55/2.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.55/2.76  thf('64', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X2 @ 
% 2.55/2.76           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 2.55/2.76           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.55/2.76      inference('demod', [status(thm)], ['62', '63'])).
% 2.55/2.76  thf('65', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 2.55/2.76           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 2.55/2.76      inference('sup+', [status(thm)], ['59', '64'])).
% 2.55/2.76  thf('66', plain,
% 2.55/2.76      (![X18 : $i, X19 : $i]:
% 2.55/2.76         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 2.55/2.76           = (k2_xboole_0 @ X18 @ X19))),
% 2.55/2.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.55/2.76  thf(commutativity_k3_xboole_0, axiom,
% 2.55/2.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.55/2.76  thf('67', plain,
% 2.55/2.76      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.55/2.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.55/2.76  thf('68', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 2.55/2.76           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.55/2.76      inference('demod', [status(thm)], ['65', '66', '67'])).
% 2.55/2.76  thf('69', plain,
% 2.55/2.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 2.55/2.76           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 2.55/2.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.55/2.76  thf('70', plain,
% 2.55/2.76      (![X16 : $i]:
% 2.55/2.76         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 2.55/2.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.55/2.76  thf(d5_xboole_0, axiom,
% 2.55/2.76    (![A:$i,B:$i,C:$i]:
% 2.55/2.76     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.55/2.76       ( ![D:$i]:
% 2.55/2.76         ( ( r2_hidden @ D @ C ) <=>
% 2.55/2.76           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.55/2.76  thf('71', plain,
% 2.55/2.76      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.55/2.76         (~ (r2_hidden @ X8 @ X7)
% 2.55/2.76          | (r2_hidden @ X8 @ X5)
% 2.55/2.76          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 2.55/2.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.55/2.76  thf('72', plain,
% 2.55/2.76      (![X5 : $i, X6 : $i, X8 : $i]:
% 2.55/2.76         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 2.55/2.76      inference('simplify', [status(thm)], ['71'])).
% 2.55/2.76  thf('73', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.55/2.76          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 2.55/2.76      inference('sup-', [status(thm)], ['70', '72'])).
% 2.55/2.76  thf('74', plain,
% 2.55/2.76      (![X16 : $i]:
% 2.55/2.76         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 2.55/2.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.55/2.76  thf('75', plain,
% 2.55/2.76      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.55/2.76         (~ (r2_hidden @ X8 @ X7)
% 2.55/2.76          | ~ (r2_hidden @ X8 @ X6)
% 2.55/2.76          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 2.55/2.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.55/2.76  thf('76', plain,
% 2.55/2.76      (![X5 : $i, X6 : $i, X8 : $i]:
% 2.55/2.76         (~ (r2_hidden @ X8 @ X6)
% 2.55/2.76          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 2.55/2.76      inference('simplify', [status(thm)], ['75'])).
% 2.55/2.76  thf('77', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.55/2.76          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['74', '76'])).
% 2.55/2.76  thf('78', plain,
% 2.55/2.76      (![X0 : $i]:
% 2.55/2.76         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 2.55/2.76          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 2.55/2.76      inference('sup-', [status(thm)], ['73', '77'])).
% 2.55/2.76  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.55/2.76      inference('simplify', [status(thm)], ['78'])).
% 2.55/2.76  thf('80', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 2.55/2.76           = (k1_xboole_0))),
% 2.55/2.76      inference('sup+', [status(thm)], ['69', '79'])).
% 2.55/2.76  thf('81', plain,
% 2.55/2.76      (![X18 : $i, X19 : $i]:
% 2.55/2.76         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 2.55/2.76           = (k2_xboole_0 @ X18 @ X19))),
% 2.55/2.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.55/2.76  thf('82', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 2.55/2.76      inference('demod', [status(thm)], ['80', '81'])).
% 2.55/2.76  thf('83', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.55/2.76      inference('demod', [status(thm)], ['68', '82'])).
% 2.55/2.76  thf('84', plain,
% 2.55/2.76      (![X12 : $i, X13 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X12 @ X13)
% 2.55/2.76          | (r2_hidden @ (sk_C @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 2.55/2.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.55/2.76  thf('85', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.55/2.76      inference('simplify', [status(thm)], ['78'])).
% 2.55/2.76  thf('86', plain,
% 2.55/2.76      (![X29 : $i, X30 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 2.55/2.76           = (k3_xboole_0 @ X29 @ X30))),
% 2.55/2.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.55/2.76  thf('87', plain,
% 2.55/2.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.55/2.76      inference('sup+', [status(thm)], ['85', '86'])).
% 2.55/2.76  thf('88', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 2.55/2.76      inference('cnf', [status(esa)], [t3_boole])).
% 2.55/2.76  thf('89', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.55/2.76      inference('demod', [status(thm)], ['87', '88'])).
% 2.55/2.76  thf('90', plain,
% 2.55/2.76      (![X12 : $i, X14 : $i, X15 : $i]:
% 2.55/2.76         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 2.55/2.76          | ~ (r1_xboole_0 @ X12 @ X15))),
% 2.55/2.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.55/2.76  thf('91', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['89', '90'])).
% 2.55/2.76  thf('92', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X1 @ X0)
% 2.55/2.76          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.55/2.76      inference('sup-', [status(thm)], ['84', '91'])).
% 2.55/2.76  thf('93', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 2.55/2.76             k1_xboole_0)
% 2.55/2.76          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.55/2.76      inference('sup-', [status(thm)], ['83', '92'])).
% 2.55/2.76  thf('94', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.55/2.76      inference('demod', [status(thm)], ['68', '82'])).
% 2.55/2.76  thf('95', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.55/2.76          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 2.55/2.76      inference('sup-', [status(thm)], ['70', '72'])).
% 2.55/2.76  thf('96', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 2.55/2.76      inference('cnf', [status(esa)], [t3_boole])).
% 2.55/2.76  thf('97', plain,
% 2.55/2.76      (![X5 : $i, X6 : $i, X8 : $i]:
% 2.55/2.76         (~ (r2_hidden @ X8 @ X6)
% 2.55/2.76          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 2.55/2.76      inference('simplify', [status(thm)], ['75'])).
% 2.55/2.76  thf('98', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['96', '97'])).
% 2.55/2.76  thf('99', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.55/2.76      inference('condensation', [status(thm)], ['98'])).
% 2.55/2.76  thf('100', plain,
% 2.55/2.76      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['95', '99'])).
% 2.55/2.76  thf('101', plain,
% 2.55/2.76      (![X29 : $i, X30 : $i]:
% 2.55/2.76         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 2.55/2.76           = (k3_xboole_0 @ X29 @ X30))),
% 2.55/2.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.55/2.76  thf('102', plain,
% 2.55/2.76      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 2.55/2.76      inference('sup+', [status(thm)], ['100', '101'])).
% 2.55/2.76  thf('103', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X1 @ X0)
% 2.55/2.76          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.55/2.76      inference('sup-', [status(thm)], ['84', '91'])).
% 2.55/2.76  thf('104', plain,
% 2.55/2.76      (![X0 : $i]:
% 2.55/2.76         (~ (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 2.55/2.76          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.55/2.76      inference('sup-', [status(thm)], ['102', '103'])).
% 2.55/2.76  thf('105', plain,
% 2.55/2.76      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 2.55/2.76      inference('sup+', [status(thm)], ['100', '101'])).
% 2.55/2.76  thf('106', plain,
% 2.55/2.76      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 2.55/2.76      inference('split', [status(esa)], ['3'])).
% 2.55/2.76  thf('107', plain, (((r1_xboole_0 @ sk_A @ sk_B_1))),
% 2.55/2.76      inference('sat_resolution*', [status(thm)], ['2', '14', '23', '44'])).
% 2.55/2.76  thf('108', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 2.55/2.76      inference('simpl_trail', [status(thm)], ['106', '107'])).
% 2.55/2.76  thf('109', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.55/2.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.55/2.76  thf(t1_boole, axiom,
% 2.55/2.76    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.55/2.76  thf('110', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.55/2.76      inference('cnf', [status(esa)], [t1_boole])).
% 2.55/2.76  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.55/2.76      inference('sup+', [status(thm)], ['109', '110'])).
% 2.55/2.76  thf('112', plain,
% 2.55/2.76      (![X34 : $i, X35 : $i]: (r1_tarski @ X34 @ (k2_xboole_0 @ X34 @ X35))),
% 2.55/2.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.55/2.76  thf('113', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.55/2.76      inference('sup+', [status(thm)], ['111', '112'])).
% 2.55/2.76  thf('114', plain,
% 2.55/2.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.55/2.76         (~ (r1_tarski @ X31 @ X32)
% 2.55/2.76          | ~ (r1_xboole_0 @ X32 @ X33)
% 2.55/2.76          | (r1_xboole_0 @ X31 @ X33))),
% 2.55/2.76      inference('cnf', [status(esa)], [t63_xboole_1])).
% 2.55/2.76  thf('115', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ k1_xboole_0 @ X1) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.55/2.76      inference('sup-', [status(thm)], ['113', '114'])).
% 2.55/2.76  thf('116', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_B_1)),
% 2.55/2.76      inference('sup-', [status(thm)], ['108', '115'])).
% 2.55/2.76  thf('117', plain,
% 2.55/2.76      (![X10 : $i, X11 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.55/2.76      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.55/2.76  thf('118', plain, ((r1_xboole_0 @ sk_B_1 @ k1_xboole_0)),
% 2.55/2.76      inference('sup-', [status(thm)], ['116', '117'])).
% 2.55/2.76  thf('119', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]:
% 2.55/2.76         ((r1_xboole_0 @ k1_xboole_0 @ X1) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.55/2.76      inference('sup-', [status(thm)], ['113', '114'])).
% 2.55/2.76  thf('120', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.55/2.76      inference('sup-', [status(thm)], ['118', '119'])).
% 2.55/2.76  thf('121', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.55/2.76      inference('demod', [status(thm)], ['104', '105', '120'])).
% 2.55/2.76  thf('122', plain,
% 2.55/2.76      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.55/2.76      inference('demod', [status(thm)], ['93', '94', '121'])).
% 2.55/2.76  thf('123', plain,
% 2.55/2.76      (![X0 : $i]:
% 2.55/2.76         (r1_xboole_0 @ sk_A @ 
% 2.55/2.76          (k2_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_A)))),
% 2.55/2.76      inference('sup+', [status(thm)], ['56', '122'])).
% 2.55/2.76  thf('124', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.55/2.76      inference('sup+', [status(thm)], ['40', '123'])).
% 2.55/2.76  thf('125', plain, ($false), inference('demod', [status(thm)], ['25', '124'])).
% 2.55/2.76  
% 2.55/2.76  % SZS output end Refutation
% 2.55/2.76  
% 2.55/2.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
