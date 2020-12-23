%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pXtOa0untr

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:49 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 152 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  650 (1230 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X30: $i] :
      ( ( ( k9_relat_1 @ X30 @ ( k1_relat_1 @ X30 ) )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k9_relat_1 @ X45 @ ( k10_relat_1 @ X45 @ X44 ) )
        = ( k3_xboole_0 @ X44 @ ( k9_relat_1 @ X45 @ ( k1_relat_1 @ X45 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('9',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k9_relat_1 @ X33 @ X31 ) @ ( k9_relat_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','30','31','32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['7','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','51'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('53',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['3','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pXtOa0untr
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/0.99  % Solved by: fo/fo7.sh
% 0.79/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.99  % done 1523 iterations in 0.508s
% 0.79/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/0.99  % SZS output start Refutation
% 0.79/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.79/0.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.79/0.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.79/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/0.99  thf(t158_funct_1, conjecture,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.79/0.99       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.79/0.99           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.79/0.99         ( r1_tarski @ A @ B ) ) ))).
% 0.79/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.99    (~( ![A:$i,B:$i,C:$i]:
% 0.79/0.99        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.79/0.99          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.79/0.99              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.79/0.99            ( r1_tarski @ A @ B ) ) ) )),
% 0.79/0.99    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.79/0.99  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(t48_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.79/0.99  thf('1', plain,
% 0.79/0.99      (![X24 : $i, X25 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.79/0.99           = (k3_xboole_0 @ X24 @ X25))),
% 0.79/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.99  thf(t36_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.79/0.99  thf('2', plain,
% 0.79/0.99      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.79/0.99      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.79/0.99  thf('3', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.79/0.99      inference('sup+', [status(thm)], ['1', '2'])).
% 0.79/0.99  thf(t146_relat_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ A ) =>
% 0.79/0.99       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.79/0.99  thf('4', plain,
% 0.79/0.99      (![X30 : $i]:
% 0.79/0.99         (((k9_relat_1 @ X30 @ (k1_relat_1 @ X30)) = (k2_relat_1 @ X30))
% 0.79/0.99          | ~ (v1_relat_1 @ X30))),
% 0.79/0.99      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.79/0.99  thf(t148_funct_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/0.99       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.79/0.99         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.79/0.99  thf('5', plain,
% 0.79/0.99      (![X44 : $i, X45 : $i]:
% 0.79/0.99         (((k9_relat_1 @ X45 @ (k10_relat_1 @ X45 @ X44))
% 0.79/0.99            = (k3_xboole_0 @ X44 @ (k9_relat_1 @ X45 @ (k1_relat_1 @ X45))))
% 0.79/0.99          | ~ (v1_funct_1 @ X45)
% 0.79/0.99          | ~ (v1_relat_1 @ X45))),
% 0.79/0.99      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.79/0.99  thf('6', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.79/0.99            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (v1_funct_1 @ X0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['4', '5'])).
% 0.79/0.99  thf('7', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (~ (v1_funct_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.79/0.99              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.79/0.99      inference('simplify', [status(thm)], ['6'])).
% 0.79/0.99  thf('8', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (~ (v1_funct_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.79/0.99              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.79/0.99      inference('simplify', [status(thm)], ['6'])).
% 0.79/0.99  thf('9', plain,
% 0.79/0.99      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(t156_relat_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ C ) =>
% 0.79/0.99       ( ( r1_tarski @ A @ B ) =>
% 0.79/0.99         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.79/0.99  thf('10', plain,
% 0.79/0.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.79/0.99         (~ (r1_tarski @ X31 @ X32)
% 0.79/0.99          | ~ (v1_relat_1 @ X33)
% 0.79/0.99          | (r1_tarski @ (k9_relat_1 @ X33 @ X31) @ (k9_relat_1 @ X33 @ X32)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.79/0.99  thf('11', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 0.79/0.99           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.79/0.99          | ~ (v1_relat_1 @ X0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['9', '10'])).
% 0.79/0.99  thf('12', plain,
% 0.79/0.99      (((r1_tarski @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) @ 
% 0.79/0.99         (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['8', '11'])).
% 0.79/0.99  thf(d10_xboole_0, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/0.99  thf('13', plain,
% 0.79/0.99      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.79/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/0.99  thf('14', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.79/0.99      inference('simplify', [status(thm)], ['13'])).
% 0.79/0.99  thf(t11_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.79/0.99  thf('15', plain,
% 0.79/0.99      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.79/0.99         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.79/0.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.79/0.99  thf('16', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.79/0.99  thf('17', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(t12_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.79/0.99  thf('18', plain,
% 0.79/0.99      (![X10 : $i, X11 : $i]:
% 0.79/0.99         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.79/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.79/0.99  thf('19', plain,
% 0.79/0.99      (((k2_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.79/0.99      inference('sup-', [status(thm)], ['17', '18'])).
% 0.79/0.99  thf('20', plain,
% 0.79/0.99      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.79/0.99         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.79/0.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.79/0.99  thf('21', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.79/0.99  thf('22', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['16', '21'])).
% 0.79/0.99  thf(t43_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.79/0.99       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.79/0.99  thf('23', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.79/0.99          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.79/0.99  thf('24', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 0.79/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/0.99  thf(t38_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.79/0.99       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.79/0.99  thf('25', plain,
% 0.79/0.99      (![X14 : $i, X15 : $i]:
% 0.79/0.99         (((X14) = (k1_xboole_0))
% 0.79/0.99          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.79/0.99  thf('26', plain,
% 0.79/0.99      (((k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (k1_xboole_0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.79/0.99  thf('27', plain,
% 0.79/0.99      (![X24 : $i, X25 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.79/0.99           = (k3_xboole_0 @ X24 @ X25))),
% 0.79/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.99  thf('28', plain,
% 0.79/0.99      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.79/0.99         = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['26', '27'])).
% 0.79/0.99  thf(t3_boole, axiom,
% 0.79/0.99    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/0.99  thf('29', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.79/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.99  thf('30', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)))),
% 0.79/0.99      inference('demod', [status(thm)], ['28', '29'])).
% 0.79/0.99  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('34', plain,
% 0.79/0.99      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.79/0.99      inference('demod', [status(thm)], ['12', '30', '31', '32', '33'])).
% 0.79/0.99  thf('35', plain,
% 0.79/0.99      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['7', '34'])).
% 0.79/0.99  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('38', plain,
% 0.79/0.99      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.79/0.99      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.79/0.99  thf('39', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.79/0.99  thf('40', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.79/0.99          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.79/0.99  thf('41', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.79/0.99      inference('sup-', [status(thm)], ['39', '40'])).
% 0.79/0.99  thf('42', plain,
% 0.79/0.99      (![X14 : $i, X15 : $i]:
% 0.79/0.99         (((X14) = (k1_xboole_0))
% 0.79/0.99          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.79/0.99  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['41', '42'])).
% 0.79/0.99  thf('44', plain,
% 0.79/0.99      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.79/0.99      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.79/0.99  thf('45', plain,
% 0.79/0.99      (![X10 : $i, X11 : $i]:
% 0.79/0.99         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.79/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.79/0.99  thf('46', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['44', '45'])).
% 0.79/0.99  thf(commutativity_k2_xboole_0, axiom,
% 0.79/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.79/0.99  thf('47', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.79/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.79/0.99  thf('48', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['46', '47'])).
% 0.79/0.99  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['43', '48'])).
% 0.79/0.99  thf('50', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.79/0.99          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.79/0.99  thf('51', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (~ (r1_tarski @ X1 @ X0)
% 0.79/0.99          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('52', plain,
% 0.79/0.99      ((r1_tarski @ 
% 0.79/0.99        (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C))) @ 
% 0.79/0.99        k1_xboole_0)),
% 0.79/0.99      inference('sup-', [status(thm)], ['38', '51'])).
% 0.79/0.99  thf(t3_xboole_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.79/0.99  thf('53', plain,
% 0.79/0.99      (![X17 : $i]:
% 0.79/0.99         (((X17) = (k1_xboole_0)) | ~ (r1_tarski @ X17 @ k1_xboole_0))),
% 0.79/0.99      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.79/0.99  thf('54', plain,
% 0.79/0.99      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.79/0.99         = (k1_xboole_0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['52', '53'])).
% 0.79/0.99  thf('55', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.79/0.99      inference('simplify', [status(thm)], ['13'])).
% 0.79/0.99  thf(t44_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.79/0.99       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.79/0.99  thf('56', plain,
% 0.79/0.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.79/0.99         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.79/0.99          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 0.79/0.99      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.79/0.99  thf('57', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['55', '56'])).
% 0.79/0.99  thf('58', plain,
% 0.79/0.99      (![X10 : $i, X11 : $i]:
% 0.79/0.99         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.79/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.79/0.99  thf('59', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.79/0.99           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['57', '58'])).
% 0.79/0.99  thf('60', plain,
% 0.79/0.99      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.79/0.99         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.79/0.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.79/0.99  thf('61', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.99         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)
% 0.79/0.99          | (r1_tarski @ X1 @ X2))),
% 0.79/0.99      inference('sup-', [status(thm)], ['59', '60'])).
% 0.79/0.99  thf('62', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (r1_tarski @ 
% 0.79/0.99             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) @ 
% 0.79/0.99              k1_xboole_0) @ 
% 0.79/0.99             X0)
% 0.79/0.99          | (r1_tarski @ sk_A @ X0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['54', '61'])).
% 0.79/0.99  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['43', '48'])).
% 0.79/0.99  thf('64', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) @ X0)
% 0.79/0.99          | (r1_tarski @ sk_A @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['62', '63'])).
% 0.79/0.99  thf('65', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.79/0.99      inference('sup-', [status(thm)], ['3', '64'])).
% 0.79/0.99  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.79/0.99  
% 0.79/0.99  % SZS output end Refutation
% 0.79/0.99  
% 0.79/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
