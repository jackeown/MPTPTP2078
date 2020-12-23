%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.StYx5j1SFJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:38 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 126 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  755 (1087 expanded)
%              Number of equality atoms :   44 (  70 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X33 @ X34 ) @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k10_relat_1 @ X24 @ X25 ) @ ( k10_relat_1 @ X23 @ X25 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k10_relat_1 @ X27 @ ( k10_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('10',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X41 @ ( k1_relat_1 @ X42 ) )
      | ( r1_tarski @ X41 @ ( k10_relat_1 @ X42 @ ( k9_relat_1 @ X42 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ ( k6_relat_1 @ X43 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['15','25'])).

thf('27',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','26'])).

thf('28',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('30',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ( ( k7_relat_1 @ X37 @ X38 )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k6_relat_1 @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','46'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','49'])).

thf('51',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','56'])).

thf('58',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.StYx5j1SFJ
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 297 iterations in 0.198s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.64  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(t88_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X33 : $i, X34 : $i]:
% 0.46/0.64         ((r1_tarski @ (k7_relat_1 @ X33 @ X34) @ X33) | ~ (v1_relat_1 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.46/0.64  thf(t179_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ![C:$i]:
% 0.46/0.64         ( ( v1_relat_1 @ C ) =>
% 0.46/0.64           ( ( r1_tarski @ B @ C ) =>
% 0.46/0.64             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X23)
% 0.46/0.64          | (r1_tarski @ (k10_relat_1 @ X24 @ X25) @ (k10_relat_1 @ X23 @ X25))
% 0.46/0.64          | ~ (r1_tarski @ X24 @ X23)
% 0.46/0.64          | ~ (v1_relat_1 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [t179_relat_1])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.46/0.64          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.46/0.64             (k10_relat_1 @ X0 @ X2))
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.46/0.64           (k10_relat_1 @ X0 @ X2))
% 0.46/0.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.64  thf(dt_k7_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.46/0.64             (k10_relat_1 @ X0 @ X2)))),
% 0.46/0.64      inference('clc', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.64      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.64  thf(t94_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X35 : $i, X36 : $i]:
% 0.46/0.64         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 0.46/0.64          | ~ (v1_relat_1 @ X36))),
% 0.46/0.64      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.46/0.64  thf(t181_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ![C:$i]:
% 0.46/0.64         ( ( v1_relat_1 @ C ) =>
% 0.46/0.64           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.46/0.64             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X26)
% 0.46/0.64          | ((k10_relat_1 @ (k5_relat_1 @ X27 @ X26) @ X28)
% 0.46/0.64              = (k10_relat_1 @ X27 @ (k10_relat_1 @ X26 @ X28)))
% 0.46/0.64          | ~ (v1_relat_1 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.46/0.64  thf(t175_funct_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ![B:$i,C:$i]:
% 0.46/0.64         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.46/0.64           ( ( k10_relat_1 @ A @ C ) =
% 0.46/0.64             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64          ( ![B:$i,C:$i]:
% 0.46/0.64            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.46/0.64              ( ( k10_relat_1 @ A @ C ) =
% 0.46/0.64                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.46/0.64  thf('10', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t71_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.64       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.64  thf('11', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf(t146_funct_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.46/0.64         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X41 : $i, X42 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X41 @ (k1_relat_1 @ X42))
% 0.46/0.64          | (r1_tarski @ X41 @ (k10_relat_1 @ X42 @ (k9_relat_1 @ X42 @ X41)))
% 0.46/0.64          | ~ (v1_relat_1 @ X42))),
% 0.46/0.64      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.64          | (r1_tarski @ X1 @ 
% 0.46/0.64             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.46/0.64              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.64  thf(fc3_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.64       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.64  thf('14', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X1 @ X0)
% 0.46/0.64          | (r1_tarski @ X1 @ 
% 0.46/0.64             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.46/0.64              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.46/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X35 : $i, X36 : $i]:
% 0.46/0.64         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 0.46/0.64          | ~ (v1_relat_1 @ X36))),
% 0.46/0.64      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.46/0.64  thf(t43_funct_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.46/0.64       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X43 : $i, X44 : $i]:
% 0.46/0.64         ((k5_relat_1 @ (k6_relat_1 @ X44) @ (k6_relat_1 @ X43))
% 0.46/0.64           = (k6_relat_1 @ (k3_xboole_0 @ X43 @ X44)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.64            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.64           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf(t148_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i]:
% 0.46/0.64         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 0.46/0.64          | ~ (v1_relat_1 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.46/0.64            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('24', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X1 @ X0)
% 0.46/0.64          | (r1_tarski @ X1 @ 
% 0.46/0.64             (k10_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1))))),
% 0.46/0.64      inference('demod', [status(thm)], ['15', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.46/0.64        (k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.46/0.64         (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '26'])).
% 0.46/0.64  thf('28', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('29', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf(t97_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.46/0.64         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X37 : $i, X38 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.46/0.64          | ((k7_relat_1 @ X37 @ X38) = (X37))
% 0.46/0.64          | ~ (v1_relat_1 @ X37))),
% 0.46/0.64      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.64          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.64  thf('32', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.64          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.64           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.64          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) = (k6_relat_1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (((k6_relat_1 @ (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.46/0.64         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['28', '35'])).
% 0.46/0.64  thf(commutativity_k2_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.64  thf(t12_setfam_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (((k6_relat_1 @ (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.46/0.64         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['36', '41'])).
% 0.46/0.64  thf('43', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (((k1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.46/0.64         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['42', '43'])).
% 0.46/0.64  thf('45', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_A @ sk_C)
% 0.46/0.64         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.46/0.64        (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '46'])).
% 0.46/0.64  thf(t1_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.64       ( r1_tarski @ A @ C ) ))).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.64          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.64          | (r1_tarski @ X3 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ X0)
% 0.46/0.64          | ~ (r1_tarski @ 
% 0.46/0.64               (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.46/0.64               X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ 
% 0.46/0.64             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C) @ 
% 0.46/0.64             X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.46/0.64          | ~ (v1_relat_1 @ sk_A)
% 0.46/0.64          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '49'])).
% 0.46/0.64  thf('51', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ 
% 0.46/0.64             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C) @ 
% 0.46/0.64             X0)
% 0.46/0.64          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C) @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ sk_A)
% 0.46/0.64          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '53'])).
% 0.46/0.64  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C) @ X0)
% 0.46/0.64          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.46/0.64        (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i, X2 : $i]:
% 0.46/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      ((~ (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.46/0.64           (k10_relat_1 @ sk_A @ sk_C))
% 0.46/0.64        | ((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.46/0.64            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_A @ sk_C)
% 0.46/0.64         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (~ (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.46/0.64          (k10_relat_1 @ sk_A @ sk_C))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain, (~ (v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '61'])).
% 0.46/0.64  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('64', plain, ($false), inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
