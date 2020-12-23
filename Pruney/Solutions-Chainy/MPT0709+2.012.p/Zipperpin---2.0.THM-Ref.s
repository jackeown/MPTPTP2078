%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aCU7l65heR

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:07 EST 2020

% Result     : Theorem 8.26s
% Output     : Refutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 216 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          : 1000 (2104 expanded)
%              Number of equality atoms :   42 ( 119 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( r1_tarski @ X30 @ ( k10_relat_1 @ X31 @ ( k9_relat_1 @ X31 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
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

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( r1_tarski @ X30 @ ( k10_relat_1 @ X31 @ ( k9_relat_1 @ X31 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X24 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('23',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k9_relat_1 @ X23 @ X21 ) @ ( k9_relat_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k10_relat_1 @ X29 @ X27 ) @ ( k10_relat_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ sk_A ) ) ) @ ( k10_relat_1 @ X2 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','42'])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k10_relat_1 @ X29 @ X27 ) @ ( k10_relat_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ X0 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('58',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X32 @ ( k2_relat_1 @ X33 ) )
      | ( ( k9_relat_1 @ X33 @ ( k10_relat_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v2_funct_1 @ X36 )
      | ~ ( r1_tarski @ X34 @ ( k1_relat_1 @ X36 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X36 @ X34 ) @ ( k9_relat_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) @ X2 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('64',plain,(
    ! [X26: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k2_relat_1 @ X26 ) )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('65',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('66',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X32 @ ( k2_relat_1 @ X33 ) )
      | ( ( k9_relat_1 @ X33 @ ( k10_relat_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k9_relat_1 @ X23 @ X21 ) @ ( k9_relat_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['63','84','85','86','87','88'])).

thf('90',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['10','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['8','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aCU7l65heR
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:09:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 8.26/8.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.26/8.44  % Solved by: fo/fo7.sh
% 8.26/8.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.26/8.44  % done 13148 iterations in 7.977s
% 8.26/8.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.26/8.44  % SZS output start Refutation
% 8.26/8.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.26/8.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.26/8.44  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 8.26/8.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.26/8.44  thf(sk_A_type, type, sk_A: $i).
% 8.26/8.44  thf(sk_B_type, type, sk_B: $i).
% 8.26/8.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.26/8.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.26/8.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.26/8.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.26/8.44  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 8.26/8.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.26/8.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 8.26/8.44  thf(t164_funct_1, conjecture,
% 8.26/8.44    (![A:$i,B:$i]:
% 8.26/8.44     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.26/8.44       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 8.26/8.44         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 8.26/8.44  thf(zf_stmt_0, negated_conjecture,
% 8.26/8.44    (~( ![A:$i,B:$i]:
% 8.26/8.44        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.26/8.44          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 8.26/8.44            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 8.26/8.44    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 8.26/8.44  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf(t146_funct_1, axiom,
% 8.26/8.44    (![A:$i,B:$i]:
% 8.26/8.44     ( ( v1_relat_1 @ B ) =>
% 8.26/8.44       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 8.26/8.44         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 8.26/8.44  thf('1', plain,
% 8.26/8.44      (![X30 : $i, X31 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X30 @ (k1_relat_1 @ X31))
% 8.26/8.44          | (r1_tarski @ X30 @ (k10_relat_1 @ X31 @ (k9_relat_1 @ X31 @ X30)))
% 8.26/8.44          | ~ (v1_relat_1 @ X31))),
% 8.26/8.44      inference('cnf', [status(esa)], [t146_funct_1])).
% 8.26/8.44  thf('2', plain,
% 8.26/8.44      ((~ (v1_relat_1 @ sk_B)
% 8.26/8.44        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 8.26/8.44      inference('sup-', [status(thm)], ['0', '1'])).
% 8.26/8.44  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('4', plain,
% 8.26/8.44      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 8.26/8.44      inference('demod', [status(thm)], ['2', '3'])).
% 8.26/8.44  thf(d10_xboole_0, axiom,
% 8.26/8.44    (![A:$i,B:$i]:
% 8.26/8.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.26/8.44  thf('5', plain,
% 8.26/8.44      (![X2 : $i, X4 : $i]:
% 8.26/8.44         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 8.26/8.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.26/8.44  thf('6', plain,
% 8.26/8.44      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 8.26/8.44        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 8.26/8.44      inference('sup-', [status(thm)], ['4', '5'])).
% 8.26/8.44  thf('7', plain,
% 8.26/8.44      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('8', plain,
% 8.26/8.44      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 8.26/8.44      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 8.26/8.44  thf('9', plain,
% 8.26/8.44      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 8.26/8.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.26/8.44  thf('10', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.26/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.26/8.44  thf(commutativity_k3_xboole_0, axiom,
% 8.26/8.44    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 8.26/8.44  thf('11', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.26/8.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.26/8.44  thf('12', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.26/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.26/8.44  thf(l32_xboole_1, axiom,
% 8.26/8.44    (![A:$i,B:$i]:
% 8.26/8.44     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.26/8.44  thf('13', plain,
% 8.26/8.44      (![X5 : $i, X7 : $i]:
% 8.26/8.44         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.26/8.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 8.26/8.44  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.26/8.44      inference('sup-', [status(thm)], ['12', '13'])).
% 8.26/8.44  thf(t48_xboole_1, axiom,
% 8.26/8.44    (![A:$i,B:$i]:
% 8.26/8.44     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.26/8.44  thf('15', plain,
% 8.26/8.44      (![X15 : $i, X16 : $i]:
% 8.26/8.44         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 8.26/8.44           = (k3_xboole_0 @ X15 @ X16))),
% 8.26/8.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.26/8.44  thf('16', plain,
% 8.26/8.44      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 8.26/8.44      inference('sup+', [status(thm)], ['14', '15'])).
% 8.26/8.44  thf(t3_boole, axiom,
% 8.26/8.44    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.26/8.44  thf('17', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 8.26/8.44      inference('cnf', [status(esa)], [t3_boole])).
% 8.26/8.44  thf('18', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 8.26/8.44      inference('demod', [status(thm)], ['16', '17'])).
% 8.26/8.44  thf('19', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.26/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.26/8.44  thf('20', plain,
% 8.26/8.44      (![X30 : $i, X31 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X30 @ (k1_relat_1 @ X31))
% 8.26/8.44          | (r1_tarski @ X30 @ (k10_relat_1 @ X31 @ (k9_relat_1 @ X31 @ X30)))
% 8.26/8.44          | ~ (v1_relat_1 @ X31))),
% 8.26/8.44      inference('cnf', [status(esa)], [t146_funct_1])).
% 8.26/8.44  thf('21', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (~ (v1_relat_1 @ X0)
% 8.26/8.44          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 8.26/8.44             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 8.26/8.44      inference('sup-', [status(thm)], ['19', '20'])).
% 8.26/8.44  thf(t167_relat_1, axiom,
% 8.26/8.44    (![A:$i,B:$i]:
% 8.26/8.44     ( ( v1_relat_1 @ B ) =>
% 8.26/8.44       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 8.26/8.44  thf('22', plain,
% 8.26/8.44      (![X24 : $i, X25 : $i]:
% 8.26/8.44         ((r1_tarski @ (k10_relat_1 @ X24 @ X25) @ (k1_relat_1 @ X24))
% 8.26/8.44          | ~ (v1_relat_1 @ X24))),
% 8.26/8.44      inference('cnf', [status(esa)], [t167_relat_1])).
% 8.26/8.44  thf('23', plain,
% 8.26/8.44      (![X2 : $i, X4 : $i]:
% 8.26/8.44         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 8.26/8.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.26/8.44  thf('24', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]:
% 8.26/8.44         (~ (v1_relat_1 @ X0)
% 8.26/8.44          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 8.26/8.44          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 8.26/8.44      inference('sup-', [status(thm)], ['22', '23'])).
% 8.26/8.44  thf('25', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (~ (v1_relat_1 @ X0)
% 8.26/8.44          | ((k1_relat_1 @ X0)
% 8.26/8.44              = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 8.26/8.44          | ~ (v1_relat_1 @ X0))),
% 8.26/8.44      inference('sup-', [status(thm)], ['21', '24'])).
% 8.26/8.44  thf('26', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (((k1_relat_1 @ X0)
% 8.26/8.44            = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 8.26/8.44          | ~ (v1_relat_1 @ X0))),
% 8.26/8.44      inference('simplify', [status(thm)], ['25'])).
% 8.26/8.44  thf('27', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.26/8.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.26/8.44  thf('28', plain,
% 8.26/8.44      (![X15 : $i, X16 : $i]:
% 8.26/8.44         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 8.26/8.44           = (k3_xboole_0 @ X15 @ X16))),
% 8.26/8.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.26/8.44  thf('29', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf(t109_xboole_1, axiom,
% 8.26/8.44    (![A:$i,B:$i,C:$i]:
% 8.26/8.44     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 8.26/8.44  thf('30', plain,
% 8.26/8.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ (k4_xboole_0 @ X8 @ X10) @ X9))),
% 8.26/8.44      inference('cnf', [status(esa)], [t109_xboole_1])).
% 8.26/8.44  thf('31', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('sup-', [status(thm)], ['29', '30'])).
% 8.26/8.44  thf('32', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('sup+', [status(thm)], ['28', '31'])).
% 8.26/8.44  thf('33', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('sup+', [status(thm)], ['27', '32'])).
% 8.26/8.44  thf(t156_relat_1, axiom,
% 8.26/8.44    (![A:$i,B:$i,C:$i]:
% 8.26/8.44     ( ( v1_relat_1 @ C ) =>
% 8.26/8.44       ( ( r1_tarski @ A @ B ) =>
% 8.26/8.44         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 8.26/8.44  thf('34', plain,
% 8.26/8.44      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X21 @ X22)
% 8.26/8.44          | ~ (v1_relat_1 @ X23)
% 8.26/8.44          | (r1_tarski @ (k9_relat_1 @ X23 @ X21) @ (k9_relat_1 @ X23 @ X22)))),
% 8.26/8.44      inference('cnf', [status(esa)], [t156_relat_1])).
% 8.26/8.44  thf('35', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]:
% 8.26/8.44         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ sk_A)) @ 
% 8.26/8.44           (k9_relat_1 @ X1 @ (k1_relat_1 @ sk_B)))
% 8.26/8.44          | ~ (v1_relat_1 @ X1))),
% 8.26/8.44      inference('sup-', [status(thm)], ['33', '34'])).
% 8.26/8.44  thf(t178_relat_1, axiom,
% 8.26/8.44    (![A:$i,B:$i,C:$i]:
% 8.26/8.44     ( ( v1_relat_1 @ C ) =>
% 8.26/8.44       ( ( r1_tarski @ A @ B ) =>
% 8.26/8.44         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 8.26/8.44  thf('36', plain,
% 8.26/8.44      (![X27 : $i, X28 : $i, X29 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X27 @ X28)
% 8.26/8.44          | ~ (v1_relat_1 @ X29)
% 8.26/8.44          | (r1_tarski @ (k10_relat_1 @ X29 @ X27) @ (k10_relat_1 @ X29 @ X28)))),
% 8.26/8.44      inference('cnf', [status(esa)], [t178_relat_1])).
% 8.26/8.44  thf('37', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.26/8.44         (~ (v1_relat_1 @ X0)
% 8.26/8.44          | (r1_tarski @ 
% 8.26/8.44             (k10_relat_1 @ X2 @ (k9_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ sk_A))) @ 
% 8.26/8.44             (k10_relat_1 @ X2 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B))))
% 8.26/8.44          | ~ (v1_relat_1 @ X2))),
% 8.26/8.44      inference('sup-', [status(thm)], ['35', '36'])).
% 8.26/8.44  thf('38', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         ((r1_tarski @ 
% 8.26/8.44           (k10_relat_1 @ sk_B @ 
% 8.26/8.44            (k9_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))) @ 
% 8.26/8.44           (k1_relat_1 @ sk_B))
% 8.26/8.44          | ~ (v1_relat_1 @ sk_B)
% 8.26/8.44          | ~ (v1_relat_1 @ sk_B)
% 8.26/8.44          | ~ (v1_relat_1 @ sk_B))),
% 8.26/8.44      inference('sup+', [status(thm)], ['26', '37'])).
% 8.26/8.44  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('42', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (r1_tarski @ 
% 8.26/8.44          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))) @ 
% 8.26/8.44          (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 8.26/8.44  thf('43', plain,
% 8.26/8.44      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 8.26/8.44        (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('sup+', [status(thm)], ['18', '42'])).
% 8.26/8.44  thf('44', plain,
% 8.26/8.44      (![X15 : $i, X16 : $i]:
% 8.26/8.44         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 8.26/8.44           = (k3_xboole_0 @ X15 @ X16))),
% 8.26/8.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.26/8.44  thf('45', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.26/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.26/8.44  thf('46', plain,
% 8.26/8.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ (k4_xboole_0 @ X8 @ X10) @ X9))),
% 8.26/8.44      inference('cnf', [status(esa)], [t109_xboole_1])).
% 8.26/8.44  thf('47', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 8.26/8.44      inference('sup-', [status(thm)], ['45', '46'])).
% 8.26/8.44  thf('48', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 8.26/8.44      inference('sup+', [status(thm)], ['44', '47'])).
% 8.26/8.44  thf('49', plain,
% 8.26/8.44      (![X27 : $i, X28 : $i, X29 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X27 @ X28)
% 8.26/8.44          | ~ (v1_relat_1 @ X29)
% 8.26/8.44          | (r1_tarski @ (k10_relat_1 @ X29 @ X27) @ (k10_relat_1 @ X29 @ X28)))),
% 8.26/8.44      inference('cnf', [status(esa)], [t178_relat_1])).
% 8.26/8.44  thf('50', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.26/8.44         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 8.26/8.44           (k10_relat_1 @ X2 @ X0))
% 8.26/8.44          | ~ (v1_relat_1 @ X2))),
% 8.26/8.44      inference('sup-', [status(thm)], ['48', '49'])).
% 8.26/8.44  thf(t1_xboole_1, axiom,
% 8.26/8.44    (![A:$i,B:$i,C:$i]:
% 8.26/8.44     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.26/8.44       ( r1_tarski @ A @ C ) ))).
% 8.26/8.44  thf('51', plain,
% 8.26/8.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X11 @ X12)
% 8.26/8.44          | ~ (r1_tarski @ X12 @ X13)
% 8.26/8.44          | (r1_tarski @ X11 @ X13))),
% 8.26/8.44      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.26/8.44  thf('52', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.26/8.44         (~ (v1_relat_1 @ X1)
% 8.26/8.44          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3)
% 8.26/8.44          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X3))),
% 8.26/8.44      inference('sup-', [status(thm)], ['50', '51'])).
% 8.26/8.44  thf('53', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         ((r1_tarski @ 
% 8.26/8.44           (k10_relat_1 @ sk_B @ 
% 8.26/8.44            (k3_xboole_0 @ (k9_relat_1 @ sk_B @ sk_A) @ X0)) @ 
% 8.26/8.44           (k1_relat_1 @ sk_B))
% 8.26/8.44          | ~ (v1_relat_1 @ sk_B))),
% 8.26/8.44      inference('sup-', [status(thm)], ['43', '52'])).
% 8.26/8.44  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('55', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (r1_tarski @ 
% 8.26/8.44          (k10_relat_1 @ sk_B @ (k3_xboole_0 @ (k9_relat_1 @ sk_B @ sk_A) @ X0)) @ 
% 8.26/8.44          (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('demod', [status(thm)], ['53', '54'])).
% 8.26/8.44  thf('56', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (r1_tarski @ 
% 8.26/8.44          (k10_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 8.26/8.44          (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('sup+', [status(thm)], ['11', '55'])).
% 8.26/8.44  thf('57', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 8.26/8.44      inference('sup+', [status(thm)], ['44', '47'])).
% 8.26/8.44  thf(t147_funct_1, axiom,
% 8.26/8.44    (![A:$i,B:$i]:
% 8.26/8.44     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.26/8.44       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 8.26/8.44         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 8.26/8.44  thf('58', plain,
% 8.26/8.44      (![X32 : $i, X33 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X32 @ (k2_relat_1 @ X33))
% 8.26/8.44          | ((k9_relat_1 @ X33 @ (k10_relat_1 @ X33 @ X32)) = (X32))
% 8.26/8.44          | ~ (v1_funct_1 @ X33)
% 8.26/8.44          | ~ (v1_relat_1 @ X33))),
% 8.26/8.44      inference('cnf', [status(esa)], [t147_funct_1])).
% 8.26/8.44  thf('59', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]:
% 8.26/8.44         (~ (v1_relat_1 @ X0)
% 8.26/8.44          | ~ (v1_funct_1 @ X0)
% 8.26/8.44          | ((k9_relat_1 @ X0 @ 
% 8.26/8.44              (k10_relat_1 @ X0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))
% 8.26/8.44              = (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))),
% 8.26/8.44      inference('sup-', [status(thm)], ['57', '58'])).
% 8.26/8.44  thf(t157_funct_1, axiom,
% 8.26/8.44    (![A:$i,B:$i,C:$i]:
% 8.26/8.44     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.26/8.44       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 8.26/8.44           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 8.26/8.44         ( r1_tarski @ A @ B ) ) ))).
% 8.26/8.44  thf('60', plain,
% 8.26/8.44      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.26/8.44         ((r1_tarski @ X34 @ X35)
% 8.26/8.44          | ~ (v1_relat_1 @ X36)
% 8.26/8.44          | ~ (v1_funct_1 @ X36)
% 8.26/8.44          | ~ (v2_funct_1 @ X36)
% 8.26/8.44          | ~ (r1_tarski @ X34 @ (k1_relat_1 @ X36))
% 8.26/8.44          | ~ (r1_tarski @ (k9_relat_1 @ X36 @ X34) @ (k9_relat_1 @ X36 @ X35)))),
% 8.26/8.44      inference('cnf', [status(esa)], [t157_funct_1])).
% 8.26/8.44  thf('61', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.26/8.44         (~ (r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 8.26/8.44             (k9_relat_1 @ X1 @ X2))
% 8.26/8.44          | ~ (v1_funct_1 @ X1)
% 8.26/8.44          | ~ (v1_relat_1 @ X1)
% 8.26/8.44          | ~ (r1_tarski @ 
% 8.26/8.44               (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)) @ 
% 8.26/8.44               (k1_relat_1 @ X1))
% 8.26/8.44          | ~ (v2_funct_1 @ X1)
% 8.26/8.44          | ~ (v1_funct_1 @ X1)
% 8.26/8.44          | ~ (v1_relat_1 @ X1)
% 8.26/8.44          | (r1_tarski @ 
% 8.26/8.44             (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)) @ X2))),
% 8.26/8.44      inference('sup-', [status(thm)], ['59', '60'])).
% 8.26/8.44  thf('62', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.26/8.44         ((r1_tarski @ 
% 8.26/8.44           (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)) @ X2)
% 8.26/8.44          | ~ (v2_funct_1 @ X1)
% 8.26/8.44          | ~ (r1_tarski @ 
% 8.26/8.44               (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)) @ 
% 8.26/8.44               (k1_relat_1 @ X1))
% 8.26/8.44          | ~ (v1_relat_1 @ X1)
% 8.26/8.44          | ~ (v1_funct_1 @ X1)
% 8.26/8.44          | ~ (r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 8.26/8.44               (k9_relat_1 @ X1 @ X2)))),
% 8.26/8.44      inference('simplify', [status(thm)], ['61'])).
% 8.26/8.44  thf('63', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (~ (r1_tarski @ 
% 8.26/8.44             (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 8.26/8.44             (k9_relat_1 @ sk_B @ X0))
% 8.26/8.44          | ~ (v1_funct_1 @ sk_B)
% 8.26/8.44          | ~ (v1_relat_1 @ sk_B)
% 8.26/8.44          | ~ (v2_funct_1 @ sk_B)
% 8.26/8.44          | (r1_tarski @ 
% 8.26/8.44             (k10_relat_1 @ sk_B @ 
% 8.26/8.44              (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 8.26/8.44             X0))),
% 8.26/8.44      inference('sup-', [status(thm)], ['56', '62'])).
% 8.26/8.44  thf(t169_relat_1, axiom,
% 8.26/8.44    (![A:$i]:
% 8.26/8.44     ( ( v1_relat_1 @ A ) =>
% 8.26/8.44       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 8.26/8.44  thf('64', plain,
% 8.26/8.44      (![X26 : $i]:
% 8.26/8.44         (((k10_relat_1 @ X26 @ (k2_relat_1 @ X26)) = (k1_relat_1 @ X26))
% 8.26/8.44          | ~ (v1_relat_1 @ X26))),
% 8.26/8.44      inference('cnf', [status(esa)], [t169_relat_1])).
% 8.26/8.44  thf('65', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.26/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.26/8.44  thf('66', plain,
% 8.26/8.44      (![X32 : $i, X33 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X32 @ (k2_relat_1 @ X33))
% 8.26/8.44          | ((k9_relat_1 @ X33 @ (k10_relat_1 @ X33 @ X32)) = (X32))
% 8.26/8.44          | ~ (v1_funct_1 @ X33)
% 8.26/8.44          | ~ (v1_relat_1 @ X33))),
% 8.26/8.44      inference('cnf', [status(esa)], [t147_funct_1])).
% 8.26/8.44  thf('67', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (~ (v1_relat_1 @ X0)
% 8.26/8.44          | ~ (v1_funct_1 @ X0)
% 8.26/8.44          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 8.26/8.44              = (k2_relat_1 @ X0)))),
% 8.26/8.44      inference('sup-', [status(thm)], ['65', '66'])).
% 8.26/8.44  thf('68', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 8.26/8.44          | ~ (v1_relat_1 @ X0)
% 8.26/8.44          | ~ (v1_funct_1 @ X0)
% 8.26/8.44          | ~ (v1_relat_1 @ X0))),
% 8.26/8.44      inference('sup+', [status(thm)], ['64', '67'])).
% 8.26/8.44  thf('69', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (~ (v1_funct_1 @ X0)
% 8.26/8.44          | ~ (v1_relat_1 @ X0)
% 8.26/8.44          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 8.26/8.44      inference('simplify', [status(thm)], ['68'])).
% 8.26/8.44  thf('70', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('71', plain,
% 8.26/8.44      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.26/8.44         (~ (r1_tarski @ X21 @ X22)
% 8.26/8.44          | ~ (v1_relat_1 @ X23)
% 8.26/8.44          | (r1_tarski @ (k9_relat_1 @ X23 @ X21) @ (k9_relat_1 @ X23 @ X22)))),
% 8.26/8.44      inference('cnf', [status(esa)], [t156_relat_1])).
% 8.26/8.44  thf('72', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ 
% 8.26/8.44           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 8.26/8.44          | ~ (v1_relat_1 @ X0))),
% 8.26/8.44      inference('sup-', [status(thm)], ['70', '71'])).
% 8.26/8.44  thf('73', plain,
% 8.26/8.44      (((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 8.26/8.44        | ~ (v1_relat_1 @ sk_B)
% 8.26/8.44        | ~ (v1_funct_1 @ sk_B)
% 8.26/8.44        | ~ (v1_relat_1 @ sk_B))),
% 8.26/8.44      inference('sup+', [status(thm)], ['69', '72'])).
% 8.26/8.44  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('77', plain,
% 8.26/8.44      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 8.26/8.44      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 8.26/8.44  thf('78', plain,
% 8.26/8.44      (![X5 : $i, X7 : $i]:
% 8.26/8.44         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.26/8.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 8.26/8.44  thf('79', plain,
% 8.26/8.44      (((k4_xboole_0 @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 8.26/8.44         = (k1_xboole_0))),
% 8.26/8.44      inference('sup-', [status(thm)], ['77', '78'])).
% 8.26/8.44  thf('80', plain,
% 8.26/8.44      (![X15 : $i, X16 : $i]:
% 8.26/8.44         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 8.26/8.44           = (k3_xboole_0 @ X15 @ X16))),
% 8.26/8.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.26/8.44  thf('81', plain,
% 8.26/8.44      (((k4_xboole_0 @ (k9_relat_1 @ sk_B @ sk_A) @ k1_xboole_0)
% 8.26/8.44         = (k3_xboole_0 @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 8.26/8.44      inference('sup+', [status(thm)], ['79', '80'])).
% 8.26/8.44  thf('82', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 8.26/8.44      inference('cnf', [status(esa)], [t3_boole])).
% 8.26/8.44  thf('83', plain,
% 8.26/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.26/8.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.26/8.44  thf('84', plain,
% 8.26/8.44      (((k9_relat_1 @ sk_B @ sk_A)
% 8.26/8.44         = (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 8.26/8.44      inference('demod', [status(thm)], ['81', '82', '83'])).
% 8.26/8.44  thf('85', plain, ((v1_funct_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('87', plain, ((v2_funct_1 @ sk_B)),
% 8.26/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.26/8.44  thf('88', plain,
% 8.26/8.44      (((k9_relat_1 @ sk_B @ sk_A)
% 8.26/8.44         = (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 8.26/8.44      inference('demod', [status(thm)], ['81', '82', '83'])).
% 8.26/8.44  thf('89', plain,
% 8.26/8.44      (![X0 : $i]:
% 8.26/8.44         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ X0))
% 8.26/8.44          | (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ X0))),
% 8.26/8.44      inference('demod', [status(thm)], ['63', '84', '85', '86', '87', '88'])).
% 8.26/8.44  thf('90', plain,
% 8.26/8.44      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 8.26/8.44      inference('sup-', [status(thm)], ['10', '89'])).
% 8.26/8.44  thf('91', plain, ($false), inference('demod', [status(thm)], ['8', '90'])).
% 8.26/8.44  
% 8.26/8.44  % SZS output end Refutation
% 8.26/8.44  
% 8.28/8.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
