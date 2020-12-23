%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bsAz0IV6CG

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:05 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 244 expanded)
%              Number of leaves         :   34 (  86 expanded)
%              Depth                    :   21
%              Number of atoms          :  944 (2351 expanded)
%              Number of equality atoms :   46 ( 115 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ X49 @ ( k1_relat_1 @ X50 ) )
      | ( r1_tarski @ X49 @ ( k10_relat_1 @ X50 @ ( k9_relat_1 @ X50 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X59 ) @ ( k6_relat_1 @ X58 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X58 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X38 @ X37 ) )
        = ( k10_relat_1 @ X38 @ ( k1_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
    ! [X39: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X39: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('23',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ X49 @ ( k1_relat_1 @ X50 ) )
      | ( r1_tarski @ X49 @ ( k10_relat_1 @ X50 @ ( k9_relat_1 @ X50 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('31',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('35',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','56'])).

thf('58',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('64',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ X51 @ ( k2_relat_1 @ X52 ) )
      | ( ( k9_relat_1 @ X52 @ ( k10_relat_1 @ X52 @ X51 ) )
        = X51 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('70',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k9_relat_1 @ X54 @ ( k10_relat_1 @ X54 @ X53 ) )
        = ( k3_xboole_0 @ X53 @ ( k9_relat_1 @ X54 @ ( k1_relat_1 @ X54 ) ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('75',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( r1_tarski @ X55 @ X56 )
      | ~ ( v1_relat_1 @ X57 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v2_funct_1 @ X57 )
      | ~ ( r1_tarski @ X55 @ ( k1_relat_1 @ X57 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X57 @ X55 ) @ ( k9_relat_1 @ X57 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ X1 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('78',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['76','81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['8','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bsAz0IV6CG
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 989 iterations in 0.618s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.08  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.08  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.90/1.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.08  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.90/1.08  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.90/1.08  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(t164_funct_1, conjecture,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.08       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.90/1.08         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i]:
% 0.90/1.08        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.08          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.90/1.08            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.90/1.08  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(t146_funct_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.90/1.08         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      (![X49 : $i, X50 : $i]:
% 0.90/1.08         (~ (r1_tarski @ X49 @ (k1_relat_1 @ X50))
% 0.90/1.08          | (r1_tarski @ X49 @ (k10_relat_1 @ X50 @ (k9_relat_1 @ X50 @ X49)))
% 0.90/1.08          | ~ (v1_relat_1 @ X50))),
% 0.90/1.08      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ sk_B)
% 0.90/1.08        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.08  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf(d10_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      (![X11 : $i, X13 : $i]:
% 0.90/1.08         (((X11) = (X13))
% 0.90/1.08          | ~ (r1_tarski @ X13 @ X11)
% 0.90/1.08          | ~ (r1_tarski @ X11 @ X13))),
% 0.90/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.90/1.08        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.90/1.08  thf(commutativity_k2_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X21 : $i, X22 : $i]:
% 0.90/1.08         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.90/1.08      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.90/1.08  thf(t12_setfam_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (![X28 : $i, X29 : $i]:
% 0.90/1.08         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 0.90/1.08      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.08      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      (![X28 : $i, X29 : $i]:
% 0.90/1.08         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 0.90/1.08      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.08      inference('sup+', [status(thm)], ['11', '12'])).
% 0.90/1.08  thf(t43_funct_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.90/1.08       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (![X58 : $i, X59 : $i]:
% 0.90/1.08         ((k5_relat_1 @ (k6_relat_1 @ X59) @ (k6_relat_1 @ X58))
% 0.90/1.08           = (k6_relat_1 @ (k3_xboole_0 @ X58 @ X59)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.90/1.08  thf(t182_relat_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ A ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( v1_relat_1 @ B ) =>
% 0.90/1.08           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.90/1.08             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (![X37 : $i, X38 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X37)
% 0.90/1.08          | ((k1_relat_1 @ (k5_relat_1 @ X38 @ X37))
% 0.90/1.08              = (k10_relat_1 @ X38 @ (k1_relat_1 @ X37)))
% 0.90/1.08          | ~ (v1_relat_1 @ X38))),
% 0.90/1.08      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.90/1.08  thf(t167_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X30 : $i, X31 : $i]:
% 0.90/1.08         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 0.90/1.08          | ~ (v1_relat_1 @ X30))),
% 0.90/1.08      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.90/1.08           (k1_relat_1 @ X1))
% 0.90/1.08          | ~ (v1_relat_1 @ X1)
% 0.90/1.08          | ~ (v1_relat_1 @ X0)
% 0.90/1.08          | ~ (v1_relat_1 @ X1))),
% 0.90/1.08      inference('sup+', [status(thm)], ['15', '16'])).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | ~ (v1_relat_1 @ X1)
% 0.90/1.08          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.90/1.08             (k1_relat_1 @ X1)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['17'])).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.90/1.08           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.90/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.90/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['14', '18'])).
% 0.90/1.08  thf(t71_relat_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.90/1.08       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.90/1.08  thf('20', plain, (![X39 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.90/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.08  thf('21', plain, (![X39 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.90/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.08  thf(fc4_funct_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.90/1.08       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.90/1.08  thf('22', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.90/1.08  thf('23', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.90/1.08  thf('24', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.90/1.08      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.90/1.08      inference('sup+', [status(thm)], ['13', '24'])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.08  thf('27', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.90/1.08      inference('simplify', [status(thm)], ['26'])).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X49 : $i, X50 : $i]:
% 0.90/1.08         (~ (r1_tarski @ X49 @ (k1_relat_1 @ X50))
% 0.90/1.08          | (r1_tarski @ X49 @ (k10_relat_1 @ X50 @ (k9_relat_1 @ X50 @ X49)))
% 0.90/1.08          | ~ (v1_relat_1 @ X50))),
% 0.90/1.08      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.90/1.08  thf('29', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.90/1.08             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.08  thf('30', plain,
% 0.90/1.08      (![X30 : $i, X31 : $i]:
% 0.90/1.08         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 0.90/1.08          | ~ (v1_relat_1 @ X30))),
% 0.90/1.08      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (![X11 : $i, X13 : $i]:
% 0.90/1.08         (((X11) = (X13))
% 0.90/1.08          | ~ (r1_tarski @ X13 @ X11)
% 0.90/1.08          | ~ (r1_tarski @ X11 @ X13))),
% 0.90/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.90/1.08          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | ((k1_relat_1 @ X0)
% 0.90/1.08              = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.90/1.08          | ~ (v1_relat_1 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['29', '32'])).
% 0.90/1.08  thf('34', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (((k1_relat_1 @ X0)
% 0.90/1.08            = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.90/1.08          | ~ (v1_relat_1 @ X0))),
% 0.90/1.08      inference('simplify', [status(thm)], ['33'])).
% 0.90/1.08  thf(t170_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( r1_tarski @
% 0.90/1.08         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 0.90/1.08  thf('35', plain,
% 0.90/1.08      (![X32 : $i, X33 : $i]:
% 0.90/1.08         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 0.90/1.08           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 0.90/1.08          | ~ (v1_relat_1 @ X32))),
% 0.90/1.08      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.90/1.08           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.90/1.08          | ~ (v1_relat_1 @ X0)
% 0.90/1.08          | ~ (v1_relat_1 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['34', '35'])).
% 0.90/1.08  thf('37', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.90/1.08             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.90/1.08      inference('simplify', [status(thm)], ['36'])).
% 0.90/1.08  thf('38', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.90/1.08          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.08  thf('39', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.90/1.08          | ~ (v1_relat_1 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.08  thf('40', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.90/1.08          | ~ (v1_relat_1 @ X0))),
% 0.90/1.08      inference('simplify', [status(thm)], ['39'])).
% 0.90/1.08  thf(d3_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.08  thf('41', plain,
% 0.90/1.08      (![X1 : $i, X3 : $i]:
% 0.90/1.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('42', plain,
% 0.90/1.08      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf('43', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.08          | (r2_hidden @ X0 @ X2)
% 0.90/1.08          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('44', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_hidden @ X0 @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.90/1.08          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['42', '43'])).
% 0.90/1.08  thf('45', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ sk_A @ X0)
% 0.90/1.08          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.90/1.08             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['41', '44'])).
% 0.90/1.08  thf('46', plain,
% 0.90/1.08      (![X32 : $i, X33 : $i]:
% 0.90/1.08         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 0.90/1.08           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 0.90/1.08          | ~ (v1_relat_1 @ X32))),
% 0.90/1.08      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.90/1.08  thf('47', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.08          | (r2_hidden @ X0 @ X2)
% 0.90/1.08          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('48', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | (r2_hidden @ X2 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.90/1.08          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X0 @ X1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['46', '47'])).
% 0.90/1.08  thf('49', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ sk_A @ X0)
% 0.90/1.08          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.90/1.08             (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.90/1.08          | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['45', '48'])).
% 0.90/1.08  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('51', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ sk_A @ X0)
% 0.90/1.08          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.90/1.08             (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.90/1.08      inference('demod', [status(thm)], ['49', '50'])).
% 0.90/1.08  thf('52', plain,
% 0.90/1.08      (![X1 : $i, X3 : $i]:
% 0.90/1.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('53', plain,
% 0.90/1.08      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.90/1.08        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['51', '52'])).
% 0.90/1.08  thf('54', plain,
% 0.90/1.08      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['53'])).
% 0.90/1.08  thf(t12_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.90/1.08  thf('55', plain,
% 0.90/1.08      (![X16 : $i, X17 : $i]:
% 0.90/1.08         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.90/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.08  thf('56', plain,
% 0.90/1.08      (((k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.90/1.09         = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.09  thf('57', plain,
% 0.90/1.09      ((((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.90/1.09          = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.09      inference('sup+', [status(thm)], ['40', '56'])).
% 0.90/1.09  thf('58', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('59', plain,
% 0.90/1.09      (![X16 : $i, X17 : $i]:
% 0.90/1.09         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.90/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.09  thf('60', plain,
% 0.90/1.09      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.09  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('62', plain,
% 0.90/1.09      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.90/1.09  thf('63', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.90/1.09      inference('simplify', [status(thm)], ['26'])).
% 0.90/1.09  thf(t147_funct_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.09       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.90/1.09         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.90/1.09  thf('64', plain,
% 0.90/1.09      (![X51 : $i, X52 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X51 @ (k2_relat_1 @ X52))
% 0.90/1.09          | ((k9_relat_1 @ X52 @ (k10_relat_1 @ X52 @ X51)) = (X51))
% 0.90/1.09          | ~ (v1_funct_1 @ X52)
% 0.90/1.09          | ~ (v1_relat_1 @ X52))),
% 0.90/1.09      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.90/1.09  thf('65', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X0)
% 0.90/1.09          | ~ (v1_funct_1 @ X0)
% 0.90/1.09          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.90/1.09              = (k2_relat_1 @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.09  thf('66', plain,
% 0.90/1.09      ((((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.90/1.09        | ~ (v1_funct_1 @ sk_B)
% 0.90/1.09        | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.09      inference('sup+', [status(thm)], ['62', '65'])).
% 0.90/1.09  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('69', plain,
% 0.90/1.09      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.90/1.09  thf(t148_funct_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.09       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.90/1.09         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.90/1.09  thf('70', plain,
% 0.90/1.09      (![X53 : $i, X54 : $i]:
% 0.90/1.09         (((k9_relat_1 @ X54 @ (k10_relat_1 @ X54 @ X53))
% 0.90/1.09            = (k3_xboole_0 @ X53 @ (k9_relat_1 @ X54 @ (k1_relat_1 @ X54))))
% 0.90/1.09          | ~ (v1_funct_1 @ X54)
% 0.90/1.09          | ~ (v1_relat_1 @ X54))),
% 0.90/1.09      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.90/1.09  thf('71', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 0.90/1.09            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B)
% 0.90/1.09          | ~ (v1_funct_1 @ sk_B))),
% 0.90/1.09      inference('sup+', [status(thm)], ['69', '70'])).
% 0.90/1.09  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('74', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 0.90/1.09           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.90/1.09  thf(t157_funct_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.09       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.90/1.09           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.09         ( r1_tarski @ A @ B ) ) ))).
% 0.90/1.09  thf('75', plain,
% 0.90/1.09      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.90/1.09         ((r1_tarski @ X55 @ X56)
% 0.90/1.09          | ~ (v1_relat_1 @ X57)
% 0.90/1.09          | ~ (v1_funct_1 @ X57)
% 0.90/1.09          | ~ (v2_funct_1 @ X57)
% 0.90/1.09          | ~ (r1_tarski @ X55 @ (k1_relat_1 @ X57))
% 0.90/1.09          | ~ (r1_tarski @ (k9_relat_1 @ X57 @ X55) @ (k9_relat_1 @ X57 @ X56)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t157_funct_1])).
% 0.90/1.09  thf('76', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 0.90/1.09             (k9_relat_1 @ sk_B @ X1))
% 0.90/1.09          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 0.90/1.09          | ~ (v2_funct_1 @ sk_B)
% 0.90/1.09          | ~ (v1_funct_1 @ sk_B)
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B)
% 0.90/1.09          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['74', '75'])).
% 0.90/1.09  thf('77', plain,
% 0.90/1.09      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.90/1.09  thf('78', plain,
% 0.90/1.09      (![X32 : $i, X33 : $i]:
% 0.90/1.09         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 0.90/1.09           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 0.90/1.09          | ~ (v1_relat_1 @ X32))),
% 0.90/1.09      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.90/1.09  thf('79', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 0.90/1.09          | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.09      inference('sup+', [status(thm)], ['77', '78'])).
% 0.90/1.09  thf('80', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('81', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['79', '80'])).
% 0.90/1.09  thf('82', plain, ((v2_funct_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('85', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 0.90/1.09             (k9_relat_1 @ sk_B @ X1))
% 0.90/1.09          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 0.90/1.09      inference('demod', [status(thm)], ['76', '81', '82', '83', '84'])).
% 0.90/1.09  thf('86', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) @ X0)),
% 0.90/1.09      inference('sup-', [status(thm)], ['25', '85'])).
% 0.90/1.09  thf('87', plain, ($false), inference('demod', [status(thm)], ['8', '86'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
