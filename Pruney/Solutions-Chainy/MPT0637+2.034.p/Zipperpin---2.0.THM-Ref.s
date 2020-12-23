%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QJ8VOY90Cw

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:00 EST 2020

% Result     : Theorem 11.69s
% Output     : Refutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  137 (1570 expanded)
%              Number of leaves         :   29 ( 537 expanded)
%              Depth                    :   26
%              Number of atoms          : 1193 (13974 expanded)
%              Number of equality atoms :   89 (1087 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ( ( k7_relat_1 @ X37 @ X38 )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ( ( k7_relat_1 @ X37 @ X38 )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('24',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) @ X22 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('33',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) @ X22 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','56'])).

thf('58',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','68'])).

thf('70',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('71',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['57','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','56'])).

thf('78',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('81',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('82',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X30 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('87',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('88',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92'])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('94',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','56'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','104'])).

thf('106',plain,(
    $false ),
    inference(simplify,[status(thm)],['105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QJ8VOY90Cw
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 11.69/11.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.69/11.88  % Solved by: fo/fo7.sh
% 11.69/11.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.69/11.88  % done 6546 iterations in 11.429s
% 11.69/11.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.69/11.88  % SZS output start Refutation
% 11.69/11.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.69/11.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 11.69/11.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.69/11.88  thf(sk_B_type, type, sk_B: $i).
% 11.69/11.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 11.69/11.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.69/11.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.69/11.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 11.69/11.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.69/11.88  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 11.69/11.88  thf(sk_A_type, type, sk_A: $i).
% 11.69/11.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.69/11.88  thf(t94_relat_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( v1_relat_1 @ B ) =>
% 11.69/11.88       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 11.69/11.88  thf('0', plain,
% 11.69/11.88      (![X35 : $i, X36 : $i]:
% 11.69/11.88         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 11.69/11.88          | ~ (v1_relat_1 @ X36))),
% 11.69/11.88      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.69/11.88  thf(t43_funct_1, conjecture,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 11.69/11.88       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 11.69/11.88  thf(zf_stmt_0, negated_conjecture,
% 11.69/11.88    (~( ![A:$i,B:$i]:
% 11.69/11.88        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 11.69/11.88          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 11.69/11.88    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 11.69/11.88  thf('1', plain,
% 11.69/11.88      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 11.69/11.88         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 11.69/11.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.69/11.88  thf('2', plain,
% 11.69/11.88      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 11.69/11.88          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 11.69/11.88        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 11.69/11.88      inference('sup-', [status(thm)], ['0', '1'])).
% 11.69/11.88  thf(fc3_funct_1, axiom,
% 11.69/11.88    (![A:$i]:
% 11.69/11.88     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 11.69/11.88       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 11.69/11.88  thf('3', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('4', plain,
% 11.69/11.88      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 11.69/11.88         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 11.69/11.88      inference('demod', [status(thm)], ['2', '3'])).
% 11.69/11.88  thf(t17_xboole_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 11.69/11.88  thf('5', plain,
% 11.69/11.88      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 11.69/11.88      inference('cnf', [status(esa)], [t17_xboole_1])).
% 11.69/11.88  thf(t71_relat_1, axiom,
% 11.69/11.88    (![A:$i]:
% 11.69/11.88     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 11.69/11.88       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 11.69/11.88  thf('6', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 11.69/11.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.69/11.88  thf(t97_relat_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( v1_relat_1 @ B ) =>
% 11.69/11.88       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 11.69/11.88         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 11.69/11.88  thf('7', plain,
% 11.69/11.88      (![X37 : $i, X38 : $i]:
% 11.69/11.88         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 11.69/11.88          | ((k7_relat_1 @ X37 @ X38) = (X37))
% 11.69/11.88          | ~ (v1_relat_1 @ X37))),
% 11.69/11.88      inference('cnf', [status(esa)], [t97_relat_1])).
% 11.69/11.88  thf('8', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (~ (r1_tarski @ X0 @ X1)
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.69/11.88          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('sup-', [status(thm)], ['6', '7'])).
% 11.69/11.88  thf('9', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('10', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (~ (r1_tarski @ X0 @ X1)
% 11.69/11.88          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('demod', [status(thm)], ['8', '9'])).
% 11.69/11.88  thf('11', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 11.69/11.88           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.88      inference('sup-', [status(thm)], ['5', '10'])).
% 11.69/11.88  thf('12', plain,
% 11.69/11.88      (![X35 : $i, X36 : $i]:
% 11.69/11.88         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 11.69/11.88          | ~ (v1_relat_1 @ X36))),
% 11.69/11.88      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.69/11.88  thf(commutativity_k3_xboole_0, axiom,
% 11.69/11.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 11.69/11.88  thf('13', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.69/11.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.88  thf('14', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 11.69/11.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.69/11.88  thf(t90_relat_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( v1_relat_1 @ B ) =>
% 11.69/11.88       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 11.69/11.88         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 11.69/11.88  thf('15', plain,
% 11.69/11.88      (![X33 : $i, X34 : $i]:
% 11.69/11.88         (((k1_relat_1 @ (k7_relat_1 @ X33 @ X34))
% 11.69/11.88            = (k3_xboole_0 @ (k1_relat_1 @ X33) @ X34))
% 11.69/11.88          | ~ (v1_relat_1 @ X33))),
% 11.69/11.88      inference('cnf', [status(esa)], [t90_relat_1])).
% 11.69/11.88  thf('16', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 11.69/11.88            = (k3_xboole_0 @ X0 @ X1))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['14', '15'])).
% 11.69/11.88  thf('17', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('18', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 11.69/11.88           = (k3_xboole_0 @ X0 @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['16', '17'])).
% 11.69/11.88  thf(d10_xboole_0, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.69/11.88  thf('19', plain,
% 11.69/11.88      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 11.69/11.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.69/11.88  thf('20', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 11.69/11.88      inference('simplify', [status(thm)], ['19'])).
% 11.69/11.88  thf('21', plain,
% 11.69/11.88      (![X37 : $i, X38 : $i]:
% 11.69/11.88         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 11.69/11.88          | ((k7_relat_1 @ X37 @ X38) = (X37))
% 11.69/11.88          | ~ (v1_relat_1 @ X37))),
% 11.69/11.88      inference('cnf', [status(esa)], [t97_relat_1])).
% 11.69/11.88  thf('22', plain,
% 11.69/11.88      (![X0 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 11.69/11.88      inference('sup-', [status(thm)], ['20', '21'])).
% 11.69/11.88  thf('23', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 11.69/11.88            (k3_xboole_0 @ X1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['18', '22'])).
% 11.69/11.88  thf(t80_relat_1, axiom,
% 11.69/11.88    (![A:$i]:
% 11.69/11.88     ( ( v1_relat_1 @ A ) =>
% 11.69/11.88       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 11.69/11.88  thf('24', plain,
% 11.69/11.88      (![X32 : $i]:
% 11.69/11.88         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 11.69/11.88          | ~ (v1_relat_1 @ X32))),
% 11.69/11.88      inference('cnf', [status(esa)], [t80_relat_1])).
% 11.69/11.88  thf('25', plain,
% 11.69/11.88      (![X35 : $i, X36 : $i]:
% 11.69/11.88         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 11.69/11.88          | ~ (v1_relat_1 @ X36))),
% 11.69/11.88      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.69/11.88  thf('26', plain,
% 11.69/11.88      (![X0 : $i]:
% 11.69/11.88         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 11.69/11.88            = (k6_relat_1 @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 11.69/11.88      inference('sup+', [status(thm)], ['24', '25'])).
% 11.69/11.88  thf('27', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 11.69/11.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.69/11.88  thf('28', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('29', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 11.69/11.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.69/11.88  thf('30', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('31', plain,
% 11.69/11.88      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 11.69/11.88      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 11.69/11.88  thf(t100_relat_1, axiom,
% 11.69/11.88    (![A:$i,B:$i,C:$i]:
% 11.69/11.88     ( ( v1_relat_1 @ C ) =>
% 11.69/11.88       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 11.69/11.88         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 11.69/11.88  thf('32', plain,
% 11.69/11.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.69/11.88         (((k7_relat_1 @ (k7_relat_1 @ X20 @ X21) @ X22)
% 11.69/11.88            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ X21 @ X22)))
% 11.69/11.88          | ~ (v1_relat_1 @ X20))),
% 11.69/11.88      inference('cnf', [status(esa)], [t100_relat_1])).
% 11.69/11.88  thf('33', plain,
% 11.69/11.88      (![X35 : $i, X36 : $i]:
% 11.69/11.88         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 11.69/11.88          | ~ (v1_relat_1 @ X36))),
% 11.69/11.88      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.69/11.88  thf(dt_k5_relat_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 11.69/11.88       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 11.69/11.88  thf('34', plain,
% 11.69/11.88      (![X18 : $i, X19 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ X18)
% 11.69/11.88          | ~ (v1_relat_1 @ X19)
% 11.69/11.88          | (v1_relat_1 @ (k5_relat_1 @ X18 @ X19)))),
% 11.69/11.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 11.69/11.88  thf('35', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ X1)
% 11.69/11.88          | ~ (v1_relat_1 @ X1)
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['33', '34'])).
% 11.69/11.88  thf('36', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('37', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ X1)
% 11.69/11.88          | ~ (v1_relat_1 @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['35', '36'])).
% 11.69/11.88  thf('38', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 11.69/11.88      inference('simplify', [status(thm)], ['37'])).
% 11.69/11.88  thf('39', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.88         ((v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ X2)
% 11.69/11.88          | ~ (v1_relat_1 @ X2))),
% 11.69/11.88      inference('sup+', [status(thm)], ['32', '38'])).
% 11.69/11.88  thf('40', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ X2)
% 11.69/11.88          | (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 11.69/11.88      inference('simplify', [status(thm)], ['39'])).
% 11.69/11.88  thf('41', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['31', '40'])).
% 11.69/11.88  thf('42', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('43', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['41', '42'])).
% 11.69/11.88  thf('44', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 11.69/11.88           (k3_xboole_0 @ X1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.69/11.88      inference('demod', [status(thm)], ['23', '43'])).
% 11.69/11.88  thf('45', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.69/11.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.88  thf(t47_xboole_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 11.69/11.88  thf('46', plain,
% 11.69/11.88      (![X7 : $i, X8 : $i]:
% 11.69/11.88         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 11.69/11.88           = (k4_xboole_0 @ X7 @ X8))),
% 11.69/11.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.69/11.88  thf('47', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.69/11.88           = (k4_xboole_0 @ X0 @ X1))),
% 11.69/11.88      inference('sup+', [status(thm)], ['45', '46'])).
% 11.69/11.88  thf(t48_xboole_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 11.69/11.88  thf('48', plain,
% 11.69/11.88      (![X9 : $i, X10 : $i]:
% 11.69/11.88         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.69/11.88           = (k3_xboole_0 @ X9 @ X10))),
% 11.69/11.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.69/11.88  thf('49', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 11.69/11.88           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['47', '48'])).
% 11.69/11.88  thf('50', plain,
% 11.69/11.88      (![X9 : $i, X10 : $i]:
% 11.69/11.88         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 11.69/11.88           = (k3_xboole_0 @ X9 @ X10))),
% 11.69/11.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 11.69/11.88  thf('51', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k3_xboole_0 @ X1 @ X0)
% 11.69/11.88           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.88      inference('demod', [status(thm)], ['49', '50'])).
% 11.69/11.88  thf('52', plain,
% 11.69/11.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.69/11.88         (((k7_relat_1 @ (k7_relat_1 @ X20 @ X21) @ X22)
% 11.69/11.88            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ X21 @ X22)))
% 11.69/11.88          | ~ (v1_relat_1 @ X20))),
% 11.69/11.88      inference('cnf', [status(esa)], [t100_relat_1])).
% 11.69/11.88  thf('53', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.88         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 11.69/11.88            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 11.69/11.88          | ~ (v1_relat_1 @ X2))),
% 11.69/11.88      inference('sup+', [status(thm)], ['51', '52'])).
% 11.69/11.88  thf('54', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X1)))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['44', '53'])).
% 11.69/11.88  thf('55', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('56', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.88      inference('demod', [status(thm)], ['54', '55'])).
% 11.69/11.88  thf('57', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['13', '56'])).
% 11.69/11.88  thf('58', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 11.69/11.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.69/11.88  thf('59', plain,
% 11.69/11.88      (![X32 : $i]:
% 11.69/11.88         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 11.69/11.88          | ~ (v1_relat_1 @ X32))),
% 11.69/11.88      inference('cnf', [status(esa)], [t80_relat_1])).
% 11.69/11.88  thf('60', plain,
% 11.69/11.88      (![X0 : $i]:
% 11.69/11.88         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 11.69/11.88            = (k6_relat_1 @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['58', '59'])).
% 11.69/11.88  thf('61', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('62', plain,
% 11.69/11.88      (![X0 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 11.69/11.88           = (k6_relat_1 @ X0))),
% 11.69/11.88      inference('demod', [status(thm)], ['60', '61'])).
% 11.69/11.88  thf('63', plain,
% 11.69/11.88      (![X35 : $i, X36 : $i]:
% 11.69/11.88         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 11.69/11.88          | ~ (v1_relat_1 @ X36))),
% 11.69/11.88      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.69/11.88  thf(t55_relat_1, axiom,
% 11.69/11.88    (![A:$i]:
% 11.69/11.88     ( ( v1_relat_1 @ A ) =>
% 11.69/11.88       ( ![B:$i]:
% 11.69/11.88         ( ( v1_relat_1 @ B ) =>
% 11.69/11.88           ( ![C:$i]:
% 11.69/11.88             ( ( v1_relat_1 @ C ) =>
% 11.69/11.88               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 11.69/11.88                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 11.69/11.88  thf('64', plain,
% 11.69/11.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ X23)
% 11.69/11.88          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 11.69/11.88              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 11.69/11.88          | ~ (v1_relat_1 @ X25)
% 11.69/11.88          | ~ (v1_relat_1 @ X24))),
% 11.69/11.88      inference('cnf', [status(esa)], [t55_relat_1])).
% 11.69/11.88  thf('65', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.88         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.69/11.88            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 11.69/11.88          | ~ (v1_relat_1 @ X1)
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ X2)
% 11.69/11.88          | ~ (v1_relat_1 @ X1))),
% 11.69/11.88      inference('sup+', [status(thm)], ['63', '64'])).
% 11.69/11.88  thf('66', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('67', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.88         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.69/11.88            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 11.69/11.88          | ~ (v1_relat_1 @ X1)
% 11.69/11.88          | ~ (v1_relat_1 @ X2)
% 11.69/11.88          | ~ (v1_relat_1 @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['65', '66'])).
% 11.69/11.88  thf('68', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ X2)
% 11.69/11.88          | ~ (v1_relat_1 @ X1)
% 11.69/11.88          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.69/11.88              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 11.69/11.88      inference('simplify', [status(thm)], ['67'])).
% 11.69/11.88  thf('69', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.69/11.88            (k6_relat_1 @ X0))
% 11.69/11.88            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['62', '68'])).
% 11.69/11.88  thf('70', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('71', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('72', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.69/11.88           (k6_relat_1 @ X0))
% 11.69/11.88           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('demod', [status(thm)], ['69', '70', '71'])).
% 11.69/11.88  thf('73', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 11.69/11.88           (k6_relat_1 @ X1))
% 11.69/11.88           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 11.69/11.88              (k6_relat_1 @ X1)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['57', '72'])).
% 11.69/11.88  thf('74', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.69/11.88           (k6_relat_1 @ X0))
% 11.69/11.88           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 11.69/11.88      inference('demod', [status(thm)], ['69', '70', '71'])).
% 11.69/11.88  thf('75', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.69/11.88           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 11.69/11.88              (k6_relat_1 @ X1)))),
% 11.69/11.88      inference('demod', [status(thm)], ['73', '74'])).
% 11.69/11.88  thf('76', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.69/11.88            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['12', '75'])).
% 11.69/11.88  thf('77', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['13', '56'])).
% 11.69/11.88  thf('78', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('79', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.69/11.88      inference('demod', [status(thm)], ['76', '77', '78'])).
% 11.69/11.88  thf('80', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ X2)
% 11.69/11.88          | ~ (v1_relat_1 @ X1)
% 11.69/11.88          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.69/11.88              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 11.69/11.88      inference('simplify', [status(thm)], ['67'])).
% 11.69/11.88  thf('81', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 11.69/11.88      inference('simplify', [status(thm)], ['19'])).
% 11.69/11.88  thf(t77_relat_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( v1_relat_1 @ B ) =>
% 11.69/11.88       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 11.69/11.88         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 11.69/11.88  thf('82', plain,
% 11.69/11.88      (![X30 : $i, X31 : $i]:
% 11.69/11.88         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 11.69/11.88          | ((k5_relat_1 @ (k6_relat_1 @ X31) @ X30) = (X30))
% 11.69/11.88          | ~ (v1_relat_1 @ X30))),
% 11.69/11.88      inference('cnf', [status(esa)], [t77_relat_1])).
% 11.69/11.88  thf('83', plain,
% 11.69/11.88      (![X0 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ X0)
% 11.69/11.88          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 11.69/11.88      inference('sup-', [status(thm)], ['81', '82'])).
% 11.69/11.88  thf('84', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (((k5_relat_1 @ 
% 11.69/11.88            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 11.69/11.88            = (k5_relat_1 @ X1 @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ X1)
% 11.69/11.88          | ~ (v1_relat_1 @ X0)
% 11.69/11.88          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['80', '83'])).
% 11.69/11.88  thf('85', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 11.69/11.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.69/11.88          | ((k5_relat_1 @ 
% 11.69/11.88              (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 11.69/11.88               (k1_relat_1 @ 
% 11.69/11.88                (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))) @ 
% 11.69/11.88              (k6_relat_1 @ X1))
% 11.69/11.88              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 11.69/11.88      inference('sup-', [status(thm)], ['79', '84'])).
% 11.69/11.88  thf('86', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['41', '42'])).
% 11.69/11.88  thf('87', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('88', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 11.69/11.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 11.69/11.88  thf('89', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.69/11.88      inference('demod', [status(thm)], ['76', '77', '78'])).
% 11.69/11.88  thf('90', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 11.69/11.88           = (k3_xboole_0 @ X0 @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['16', '17'])).
% 11.69/11.88  thf('91', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.88      inference('demod', [status(thm)], ['54', '55'])).
% 11.69/11.88  thf('92', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.69/11.88      inference('demod', [status(thm)], ['76', '77', '78'])).
% 11.69/11.88  thf('93', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.69/11.88           (k6_relat_1 @ X1)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.69/11.88      inference('demod', [status(thm)],
% 11.69/11.88                ['85', '86', '87', '88', '89', '90', '91', '92'])).
% 11.69/11.88  thf(t76_relat_1, axiom,
% 11.69/11.88    (![A:$i,B:$i]:
% 11.69/11.88     ( ( v1_relat_1 @ B ) =>
% 11.69/11.88       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 11.69/11.88         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 11.69/11.88  thf('94', plain,
% 11.69/11.88      (![X28 : $i, X29 : $i]:
% 11.69/11.88         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 11.69/11.88          | ~ (v1_relat_1 @ X28))),
% 11.69/11.88      inference('cnf', [status(esa)], [t76_relat_1])).
% 11.69/11.88  thf('95', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 11.69/11.88           (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 11.69/11.88          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['93', '94'])).
% 11.69/11.88  thf('96', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['41', '42'])).
% 11.69/11.88  thf('97', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 11.69/11.88          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['95', '96'])).
% 11.69/11.88  thf('98', plain,
% 11.69/11.88      (![X2 : $i, X4 : $i]:
% 11.69/11.88         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 11.69/11.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.69/11.88  thf('99', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 11.69/11.88             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 11.69/11.88          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 11.69/11.88      inference('sup-', [status(thm)], ['97', '98'])).
% 11.69/11.88  thf('100', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 11.69/11.88          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['95', '96'])).
% 11.69/11.88  thf('101', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.69/11.88      inference('demod', [status(thm)], ['99', '100'])).
% 11.69/11.88  thf('102', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 11.69/11.88           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.88      inference('demod', [status(thm)], ['11', '101'])).
% 11.69/11.88  thf('103', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['13', '56'])).
% 11.69/11.88  thf('104', plain,
% 11.69/11.88      (![X0 : $i, X1 : $i]:
% 11.69/11.88         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 11.69/11.88           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.69/11.88      inference('sup+', [status(thm)], ['102', '103'])).
% 11.69/11.88  thf('105', plain,
% 11.69/11.88      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 11.69/11.88         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 11.69/11.88      inference('demod', [status(thm)], ['4', '104'])).
% 11.69/11.88  thf('106', plain, ($false), inference('simplify', [status(thm)], ['105'])).
% 11.69/11.88  
% 11.69/11.88  % SZS output end Refutation
% 11.69/11.88  
% 11.69/11.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
