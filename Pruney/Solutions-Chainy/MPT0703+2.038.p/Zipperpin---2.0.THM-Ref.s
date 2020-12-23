%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GaECsz5gOz

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:54 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 234 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  649 (1933 expanded)
%              Number of equality atoms :   44 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','12'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ( ( k7_relat_1 @ X27 @ X28 )
        = X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16','22'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','21'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('28',plain,(
    ! [X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','21'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','34','35'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k9_relat_1 @ X34 @ ( k10_relat_1 @ X34 @ X33 ) )
        = ( k3_xboole_0 @ X33 @ ( k9_relat_1 @ X34 @ ( k1_relat_1 @ X34 ) ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','34','35'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','21'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('43',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['5','49','50'])).

thf('52',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C_1 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C_1 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    = ( k10_relat_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t149_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf('55',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X35 @ ( k3_xboole_0 @ X36 @ ( k10_relat_1 @ X35 @ X37 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X35 @ X36 ) @ X37 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t149_funct_1])).

thf('56',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_A ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('58',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','62','63','64','65'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['51','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GaECsz5gOz
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:24:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 155 iterations in 0.094s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.56  thf(t158_funct_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.37/0.56           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.37/0.56         ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.37/0.56              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.37/0.56            ( r1_tarski @ A @ B ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.37/0.56  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.56  thf('1', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.56  thf(t12_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.56  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf(t31_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( r1_tarski @
% 0.37/0.56       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.37/0.56       ( k2_xboole_0 @ B @ C ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.56         (r1_tarski @ 
% 0.37/0.56          (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)) @ 
% 0.37/0.56          (k2_xboole_0 @ X9 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (r1_tarski @ 
% 0.37/0.56          (k2_xboole_0 @ (k3_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.37/0.56           (k3_xboole_0 @ X1 @ X0)) @ 
% 0.37/0.56          X0)),
% 0.37/0.56      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t110_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X18 : $i]:
% 0.37/0.56         (((k7_relat_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.37/0.56  thf(t87_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X25 : $i, X26 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X25 @ X26)) @ X26)
% 0.37/0.56          | ~ (v1_relat_1 @ X25))),
% 0.37/0.56      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.37/0.56  thf(t3_xboole_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         (((X11) = (k1_xboole_0)) | ~ (r1_tarski @ X11 @ k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['7', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0) | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.56  thf('13', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '12'])).
% 0.37/0.56  thf(t97_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.37/0.56         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X27 : $i, X28 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 0.37/0.56          | ((k7_relat_1 @ X27 @ X28) = (X27))
% 0.37/0.56          | ~ (v1_relat_1 @ X27))),
% 0.37/0.56      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.56          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf('16', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.56  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X18 : $i]:
% 0.37/0.56         (((k7_relat_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.37/0.56  thf(dt_k7_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X16 : $i, X17 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_relat_1 @ k1_xboole_0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.56  thf('22', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16', '22'])).
% 0.37/0.56  thf(t148_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 0.37/0.56          | ~ (v1_relat_1 @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '21'])).
% 0.37/0.56  thf(t149_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X22 : $i]:
% 0.37/0.56         (((k9_relat_1 @ X22 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X18 : $i]:
% 0.37/0.56         (((k7_relat_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 0.37/0.56          | ~ (v1_relat_1 @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['27', '31'])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0) | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.37/0.56  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['26', '33'])).
% 0.37/0.56  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '21'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['25', '34', '35'])).
% 0.37/0.56  thf(t148_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.37/0.56         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X33 : $i, X34 : $i]:
% 0.37/0.56         (((k9_relat_1 @ X34 @ (k10_relat_1 @ X34 @ X33))
% 0.37/0.56            = (k3_xboole_0 @ X33 @ (k9_relat_1 @ X34 @ (k1_relat_1 @ X34))))
% 0.37/0.56          | ~ (v1_funct_1 @ X34)
% 0.37/0.56          | ~ (v1_relat_1 @ X34))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k9_relat_1 @ k1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.56            = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.56          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['25', '34', '35'])).
% 0.37/0.56  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '21'])).
% 0.37/0.56  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X18 : $i]:
% 0.37/0.56         (((k7_relat_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.37/0.56  thf(fc8_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.56       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.37/0.56         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X29 : $i, X30 : $i]:
% 0.37/0.56         (~ (v1_funct_1 @ X29)
% 0.37/0.56          | ~ (v1_relat_1 @ X29)
% 0.37/0.56          | (v1_funct_1 @ (k7_relat_1 @ X29 @ X30)))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_funct_1 @ k1_xboole_0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_funct_1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_funct_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | (v1_funct_1 @ k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.56  thf('46', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_funct_1 @ sk_C_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['41', '45'])).
% 0.37/0.56  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('48', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.37/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['38', '39', '40', '48'])).
% 0.37/0.56  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.37/0.56      inference('demod', [status(thm)], ['5', '49', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      ((r1_tarski @ (k10_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.37/0.56        (k10_relat_1 @ sk_C_1 @ sk_B))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t28_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (((k3_xboole_0 @ (k10_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.37/0.56         (k10_relat_1 @ sk_C_1 @ sk_B)) = (k10_relat_1 @ sk_C_1 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.56  thf(t149_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56       ( r1_tarski @
% 0.37/0.56         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 0.37/0.56         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.56         ((r1_tarski @ 
% 0.37/0.56           (k9_relat_1 @ X35 @ (k3_xboole_0 @ X36 @ (k10_relat_1 @ X35 @ X37))) @ 
% 0.37/0.56           (k3_xboole_0 @ (k9_relat_1 @ X35 @ X36) @ X37))
% 0.37/0.56          | ~ (v1_funct_1 @ X35)
% 0.37/0.56          | ~ (v1_relat_1 @ X35))),
% 0.37/0.56      inference('cnf', [status(esa)], [t149_funct_1])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (((r1_tarski @ (k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.37/0.56         (k3_xboole_0 @ 
% 0.37/0.56          (k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_A)) @ sk_B))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C_1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('57', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t147_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.37/0.56         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (![X31 : $i, X32 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 0.37/0.56          | ((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31)) = (X31))
% 0.37/0.56          | ~ (v1_funct_1 @ X32)
% 0.37/0.56          | ~ (v1_relat_1 @ X32))),
% 0.37/0.56      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C_1)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.56        | ((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_A)) = (sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.56  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_A)) = (sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_A)) = (sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.37/0.56  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('65', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('66', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['56', '62', '63', '64', '65'])).
% 0.37/0.56  thf(t1_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.56       ( r1_tarski @ A @ C ) ))).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X2 @ X3)
% 0.37/0.56          | ~ (r1_tarski @ X3 @ X4)
% 0.37/0.56          | (r1_tarski @ X2 @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ sk_A @ X0)
% 0.37/0.56          | ~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.56  thf('69', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('sup-', [status(thm)], ['51', '68'])).
% 0.37/0.56  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
