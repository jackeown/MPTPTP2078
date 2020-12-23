%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z9g8FvrXQR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:29 EST 2020

% Result     : Theorem 8.21s
% Output     : Refutation 8.21s
% Verified   : 
% Statistics : Number of formulae       :  239 (1649 expanded)
%              Number of leaves         :   29 ( 533 expanded)
%              Depth                    :   46
%              Number of atoms          : 2008 (14280 expanded)
%              Number of equality atoms :  156 (1352 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X39 @ ( k10_relat_1 @ X39 @ X40 ) ) @ X40 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k6_subset_1 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','34','35'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k10_relat_1 @ X36 @ ( k6_subset_1 @ X37 @ X38 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X36 @ X37 ) @ ( k10_relat_1 @ X36 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k10_relat_1 @ X36 @ ( k6_subset_1 @ X37 @ X38 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X36 @ X37 ) @ ( k10_relat_1 @ X36 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t147_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
         => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_funct_1])).

thf('43',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('45',plain,
    ( ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('47',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k10_relat_1 @ X36 @ ( k6_subset_1 @ X37 @ X38 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X36 @ X37 ) @ ( k10_relat_1 @ X36 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
      = ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('53',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('55',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k6_subset_1 @ X15 @ X17 )
       != X15 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( ( k10_relat_1 @ X34 @ X35 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('61',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k10_relat_1 @ X36 @ ( k6_subset_1 @ X37 @ X38 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X36 @ X37 ) @ ( k10_relat_1 @ X36 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k6_subset_1 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('73',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','76'])).

thf('78',plain,
    ( ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k6_subset_1 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('86',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('98',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X41 @ ( k1_relat_1 @ X42 ) )
      | ( r1_tarski @ X41 @ ( k10_relat_1 @ X42 @ ( k9_relat_1 @ X42 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['37','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k6_subset_1 @ ( k2_relat_1 @ X1 ) @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k6_subset_1 @ ( k2_relat_1 @ X1 ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ) @ ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ X0 @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('114',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('115',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X41 @ ( k1_relat_1 @ X42 ) )
      | ( r1_tarski @ X41 @ ( k10_relat_1 @ X42 @ ( k9_relat_1 @ X42 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('118',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('119',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
        = ( k10_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('123',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['116','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('129',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k10_relat_1 @ X34 @ X35 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X34 ) @ X35 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k6_subset_1 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k6_subset_1 @ ( k2_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('134',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('139',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('140',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k6_subset_1 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('143',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('146',plain,
    ( ( ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('151',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('154',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['143','154'])).

thf('156',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('157',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ X0 @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','155','156','157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('162',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('163',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['161','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['160','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('176',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['173','174','175','176','177'])).

thf('179',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k10_relat_1 @ X34 @ X35 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X34 ) @ X35 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('185',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( r1_xboole_0 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['183','186'])).

thf('188',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('189',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( r1_xboole_0 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ sk_A @ X1 ) @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k6_subset_1 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ X1 ) @ ( k6_subset_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      = ( k6_subset_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_A @ X0 )
      = ( k3_xboole_0 @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['159','197'])).

thf('199',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('200',plain,
    ( ( k6_subset_1 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('202',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( sk_A
      = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['206','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z9g8FvrXQR
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 8.21/8.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.21/8.44  % Solved by: fo/fo7.sh
% 8.21/8.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.21/8.44  % done 13329 iterations in 7.989s
% 8.21/8.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.21/8.44  % SZS output start Refutation
% 8.21/8.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.21/8.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.21/8.44  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 8.21/8.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.21/8.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.21/8.44  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 8.21/8.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.21/8.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.21/8.44  thf(sk_A_type, type, sk_A: $i).
% 8.21/8.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 8.21/8.44  thf(sk_B_type, type, sk_B: $i).
% 8.21/8.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.21/8.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.21/8.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.21/8.44  thf(t145_funct_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.21/8.44       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 8.21/8.44  thf('0', plain,
% 8.21/8.44      (![X39 : $i, X40 : $i]:
% 8.21/8.44         ((r1_tarski @ (k9_relat_1 @ X39 @ (k10_relat_1 @ X39 @ X40)) @ X40)
% 8.21/8.44          | ~ (v1_funct_1 @ X39)
% 8.21/8.44          | ~ (v1_relat_1 @ X39))),
% 8.21/8.44      inference('cnf', [status(esa)], [t145_funct_1])).
% 8.21/8.44  thf(l32_xboole_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.21/8.44  thf('1', plain,
% 8.21/8.44      (![X5 : $i, X7 : $i]:
% 8.21/8.44         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.21/8.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 8.21/8.44  thf(redefinition_k6_subset_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 8.21/8.44  thf('2', plain,
% 8.21/8.44      (![X27 : $i, X28 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 8.21/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.21/8.44  thf('3', plain,
% 8.21/8.44      (![X5 : $i, X7 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.21/8.44      inference('demod', [status(thm)], ['1', '2'])).
% 8.21/8.44  thf('4', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X1)
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 8.21/8.44              = (k1_xboole_0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['0', '3'])).
% 8.21/8.44  thf(t48_xboole_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.21/8.44  thf('5', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.21/8.44  thf('6', plain,
% 8.21/8.44      (![X27 : $i, X28 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 8.21/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.21/8.44  thf('7', plain,
% 8.21/8.44      (![X27 : $i, X28 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 8.21/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.21/8.44  thf('8', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf('9', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ 
% 8.21/8.44            k1_xboole_0)
% 8.21/8.44            = (k3_xboole_0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0))
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ~ (v1_relat_1 @ X1))),
% 8.21/8.44      inference('sup+', [status(thm)], ['4', '8'])).
% 8.21/8.44  thf('10', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf(d10_xboole_0, axiom,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.21/8.44  thf('11', plain,
% 8.21/8.44      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 8.21/8.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.21/8.44  thf('12', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.21/8.44      inference('simplify', [status(thm)], ['11'])).
% 8.21/8.44  thf('13', plain,
% 8.21/8.44      (![X5 : $i, X7 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.21/8.44      inference('demod', [status(thm)], ['1', '2'])).
% 8.21/8.44  thf('14', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['12', '13'])).
% 8.21/8.44  thf(t36_xboole_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.21/8.44  thf('15', plain,
% 8.21/8.44      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 8.21/8.44      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.21/8.44  thf('16', plain,
% 8.21/8.44      (![X27 : $i, X28 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 8.21/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.21/8.44  thf('17', plain,
% 8.21/8.44      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 8.21/8.44      inference('demod', [status(thm)], ['15', '16'])).
% 8.21/8.44  thf('18', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.21/8.44      inference('sup+', [status(thm)], ['14', '17'])).
% 8.21/8.44  thf('19', plain,
% 8.21/8.44      (![X5 : $i, X7 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.21/8.44      inference('demod', [status(thm)], ['1', '2'])).
% 8.21/8.44  thf('20', plain,
% 8.21/8.44      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['18', '19'])).
% 8.21/8.44  thf('21', plain,
% 8.21/8.44      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['10', '20'])).
% 8.21/8.44  thf(commutativity_k3_xboole_0, axiom,
% 8.21/8.44    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 8.21/8.44  thf('22', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.21/8.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.21/8.44  thf('23', plain,
% 8.21/8.44      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['21', '22'])).
% 8.21/8.44  thf('24', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf('25', plain,
% 8.21/8.44      (![X5 : $i, X6 : $i]:
% 8.21/8.44         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 8.21/8.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 8.21/8.44  thf('26', plain,
% 8.21/8.44      (![X27 : $i, X28 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 8.21/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.21/8.44  thf('27', plain,
% 8.21/8.44      (![X5 : $i, X6 : $i]:
% 8.21/8.44         ((r1_tarski @ X5 @ X6) | ((k6_subset_1 @ X5 @ X6) != (k1_xboole_0)))),
% 8.21/8.44      inference('demod', [status(thm)], ['25', '26'])).
% 8.21/8.44  thf('28', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 8.21/8.44          | (r1_tarski @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['24', '27'])).
% 8.21/8.44  thf('29', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k1_xboole_0) != (k1_xboole_0))
% 8.21/8.44          | (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ k1_xboole_0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['23', '28'])).
% 8.21/8.44  thf('30', plain,
% 8.21/8.44      (![X0 : $i]: (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['29'])).
% 8.21/8.44  thf('31', plain,
% 8.21/8.44      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 8.21/8.44      inference('demod', [status(thm)], ['15', '16'])).
% 8.21/8.44  thf('32', plain,
% 8.21/8.44      (![X2 : $i, X4 : $i]:
% 8.21/8.44         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 8.21/8.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.21/8.44  thf('33', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.21/8.44          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['31', '32'])).
% 8.21/8.44  thf('34', plain, (![X0 : $i]: ((X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['30', '33'])).
% 8.21/8.44  thf('35', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.21/8.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.21/8.44  thf('36', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 8.21/8.44            = (k3_xboole_0 @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ~ (v1_relat_1 @ X1))),
% 8.21/8.44      inference('demod', [status(thm)], ['9', '34', '35'])).
% 8.21/8.44  thf(t138_funct_1, axiom,
% 8.21/8.44    (![A:$i,B:$i,C:$i]:
% 8.21/8.44     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.21/8.44       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 8.21/8.44         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 8.21/8.44  thf('37', plain,
% 8.21/8.44      (![X36 : $i, X37 : $i, X38 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X36 @ (k6_subset_1 @ X37 @ X38))
% 8.21/8.44            = (k6_subset_1 @ (k10_relat_1 @ X36 @ X37) @ 
% 8.21/8.44               (k10_relat_1 @ X36 @ X38)))
% 8.21/8.44          | ~ (v1_funct_1 @ X36)
% 8.21/8.44          | ~ (v1_relat_1 @ X36))),
% 8.21/8.44      inference('cnf', [status(esa)], [t138_funct_1])).
% 8.21/8.44  thf(t169_relat_1, axiom,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( v1_relat_1 @ A ) =>
% 8.21/8.44       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 8.21/8.44  thf('38', plain,
% 8.21/8.44      (![X31 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 8.21/8.44          | ~ (v1_relat_1 @ X31))),
% 8.21/8.44      inference('cnf', [status(esa)], [t169_relat_1])).
% 8.21/8.44  thf('39', plain,
% 8.21/8.44      (![X36 : $i, X37 : $i, X38 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X36 @ (k6_subset_1 @ X37 @ X38))
% 8.21/8.44            = (k6_subset_1 @ (k10_relat_1 @ X36 @ X37) @ 
% 8.21/8.44               (k10_relat_1 @ X36 @ X38)))
% 8.21/8.44          | ~ (v1_funct_1 @ X36)
% 8.21/8.44          | ~ (v1_relat_1 @ X36))),
% 8.21/8.44      inference('cnf', [status(esa)], [t138_funct_1])).
% 8.21/8.44  thf('40', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X0 @ (k6_subset_1 @ (k2_relat_1 @ X0) @ X1))
% 8.21/8.44            = (k6_subset_1 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (v1_funct_1 @ X0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['38', '39'])).
% 8.21/8.44  thf('41', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_funct_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ((k10_relat_1 @ X0 @ (k6_subset_1 @ (k2_relat_1 @ X0) @ X1))
% 8.21/8.44              = (k6_subset_1 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 8.21/8.44      inference('simplify', [status(thm)], ['40'])).
% 8.21/8.44  thf('42', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['12', '13'])).
% 8.21/8.44  thf(t147_funct_1, conjecture,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.21/8.44       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 8.21/8.44         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 8.21/8.44  thf(zf_stmt_0, negated_conjecture,
% 8.21/8.44    (~( ![A:$i,B:$i]:
% 8.21/8.44        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.21/8.44          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 8.21/8.44            ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 8.21/8.44    inference('cnf.neg', [status(esa)], [t147_funct_1])).
% 8.21/8.44  thf('43', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('44', plain,
% 8.21/8.44      (![X5 : $i, X7 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.21/8.44      inference('demod', [status(thm)], ['1', '2'])).
% 8.21/8.44  thf('45', plain,
% 8.21/8.44      (((k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['43', '44'])).
% 8.21/8.44  thf('46', plain,
% 8.21/8.44      (![X31 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 8.21/8.44          | ~ (v1_relat_1 @ X31))),
% 8.21/8.44      inference('cnf', [status(esa)], [t169_relat_1])).
% 8.21/8.44  thf('47', plain,
% 8.21/8.44      (![X36 : $i, X37 : $i, X38 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X36 @ (k6_subset_1 @ X37 @ X38))
% 8.21/8.44            = (k6_subset_1 @ (k10_relat_1 @ X36 @ X37) @ 
% 8.21/8.44               (k10_relat_1 @ X36 @ X38)))
% 8.21/8.44          | ~ (v1_funct_1 @ X36)
% 8.21/8.44          | ~ (v1_relat_1 @ X36))),
% 8.21/8.44      inference('cnf', [status(esa)], [t138_funct_1])).
% 8.21/8.44  thf('48', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X0 @ (k6_subset_1 @ X1 @ (k2_relat_1 @ X0)))
% 8.21/8.44            = (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (v1_funct_1 @ X0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['46', '47'])).
% 8.21/8.44  thf('49', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_funct_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ((k10_relat_1 @ X0 @ (k6_subset_1 @ X1 @ (k2_relat_1 @ X0)))
% 8.21/8.44              = (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))))),
% 8.21/8.44      inference('simplify', [status(thm)], ['48'])).
% 8.21/8.44  thf('50', plain,
% 8.21/8.44      ((((k10_relat_1 @ sk_B @ k1_xboole_0)
% 8.21/8.44          = (k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))
% 8.21/8.44        | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44        | ~ (v1_funct_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['45', '49'])).
% 8.21/8.44  thf('51', plain,
% 8.21/8.44      (![X31 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 8.21/8.44          | ~ (v1_relat_1 @ X31))),
% 8.21/8.44      inference('cnf', [status(esa)], [t169_relat_1])).
% 8.21/8.44  thf('52', plain, (![X0 : $i]: ((X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['30', '33'])).
% 8.21/8.44  thf(t83_xboole_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 8.21/8.44  thf('53', plain,
% 8.21/8.44      (![X15 : $i, X17 : $i]:
% 8.21/8.44         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 8.21/8.44      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.21/8.44  thf('54', plain,
% 8.21/8.44      (![X27 : $i, X28 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 8.21/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.21/8.44  thf('55', plain,
% 8.21/8.44      (![X15 : $i, X17 : $i]:
% 8.21/8.44         ((r1_xboole_0 @ X15 @ X17) | ((k6_subset_1 @ X15 @ X17) != (X15)))),
% 8.21/8.44      inference('demod', [status(thm)], ['53', '54'])).
% 8.21/8.44  thf('56', plain,
% 8.21/8.44      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['52', '55'])).
% 8.21/8.44  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 8.21/8.44      inference('simplify', [status(thm)], ['56'])).
% 8.21/8.44  thf(t173_relat_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( v1_relat_1 @ B ) =>
% 8.21/8.44       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 8.21/8.44         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 8.21/8.44  thf('58', plain,
% 8.21/8.44      (![X34 : $i, X35 : $i]:
% 8.21/8.44         (~ (r1_xboole_0 @ (k2_relat_1 @ X34) @ X35)
% 8.21/8.44          | ((k10_relat_1 @ X34 @ X35) = (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ X34))),
% 8.21/8.44      inference('cnf', [status(esa)], [t173_relat_1])).
% 8.21/8.44  thf('59', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X0)
% 8.21/8.44          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['57', '58'])).
% 8.21/8.44  thf('60', plain,
% 8.21/8.44      (((k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['43', '44'])).
% 8.21/8.44  thf('61', plain,
% 8.21/8.44      (![X36 : $i, X37 : $i, X38 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X36 @ (k6_subset_1 @ X37 @ X38))
% 8.21/8.44            = (k6_subset_1 @ (k10_relat_1 @ X36 @ X37) @ 
% 8.21/8.44               (k10_relat_1 @ X36 @ X38)))
% 8.21/8.44          | ~ (v1_funct_1 @ X36)
% 8.21/8.44          | ~ (v1_relat_1 @ X36))),
% 8.21/8.44      inference('cnf', [status(esa)], [t138_funct_1])).
% 8.21/8.44  thf('62', plain,
% 8.21/8.44      (![X5 : $i, X6 : $i]:
% 8.21/8.44         ((r1_tarski @ X5 @ X6) | ((k6_subset_1 @ X5 @ X6) != (k1_xboole_0)))),
% 8.21/8.44      inference('demod', [status(thm)], ['25', '26'])).
% 8.21/8.44  thf('63', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)) != (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ X2)
% 8.21/8.44          | ~ (v1_funct_1 @ X2)
% 8.21/8.44          | (r1_tarski @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['61', '62'])).
% 8.21/8.44  thf('64', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 8.21/8.44          | (r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 8.21/8.44             (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 8.21/8.44          | ~ (v1_funct_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['60', '63'])).
% 8.21/8.44  thf('65', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k1_xboole_0) != (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (v1_funct_1 @ X0)
% 8.21/8.44          | (r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 8.21/8.44             (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['59', '64'])).
% 8.21/8.44  thf('66', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 8.21/8.44           (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 8.21/8.44          | ~ (v1_funct_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['65'])).
% 8.21/8.44  thf('67', plain,
% 8.21/8.44      (((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 8.21/8.44        | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44        | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44        | ~ (v1_funct_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['51', '66'])).
% 8.21/8.44  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('70', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('71', plain,
% 8.21/8.44      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))),
% 8.21/8.44      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 8.21/8.44  thf('72', plain,
% 8.21/8.44      (![X5 : $i, X7 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.21/8.44      inference('demod', [status(thm)], ['1', '2'])).
% 8.21/8.44  thf('73', plain,
% 8.21/8.44      (((k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 8.21/8.44         = (k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['71', '72'])).
% 8.21/8.44  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('76', plain, (((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 8.21/8.44      inference('demod', [status(thm)], ['50', '73', '74', '75'])).
% 8.21/8.44  thf('77', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['42', '76'])).
% 8.21/8.44  thf('78', plain,
% 8.21/8.44      ((((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 8.21/8.44          (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))) = (k1_xboole_0))
% 8.21/8.44        | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44        | ~ (v1_funct_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['41', '77'])).
% 8.21/8.44  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('81', plain,
% 8.21/8.44      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 8.21/8.44         (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))) = (k1_xboole_0))),
% 8.21/8.44      inference('demod', [status(thm)], ['78', '79', '80'])).
% 8.21/8.44  thf('82', plain,
% 8.21/8.44      (![X5 : $i, X6 : $i]:
% 8.21/8.44         ((r1_tarski @ X5 @ X6) | ((k6_subset_1 @ X5 @ X6) != (k1_xboole_0)))),
% 8.21/8.44      inference('demod', [status(thm)], ['25', '26'])).
% 8.21/8.44  thf('83', plain,
% 8.21/8.44      ((((k1_xboole_0) != (k1_xboole_0))
% 8.21/8.44        | (r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 8.21/8.44           (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['81', '82'])).
% 8.21/8.44  thf('84', plain,
% 8.21/8.44      ((r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 8.21/8.44        (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('simplify', [status(thm)], ['83'])).
% 8.21/8.44  thf('85', plain,
% 8.21/8.44      (![X31 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 8.21/8.44          | ~ (v1_relat_1 @ X31))),
% 8.21/8.44      inference('cnf', [status(esa)], [t169_relat_1])).
% 8.21/8.44  thf(t170_relat_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( v1_relat_1 @ B ) =>
% 8.21/8.44       ( r1_tarski @
% 8.21/8.44         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 8.21/8.44  thf('86', plain,
% 8.21/8.44      (![X32 : $i, X33 : $i]:
% 8.21/8.44         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 8.21/8.44           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 8.21/8.44          | ~ (v1_relat_1 @ X32))),
% 8.21/8.44      inference('cnf', [status(esa)], [t170_relat_1])).
% 8.21/8.44  thf('87', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['85', '86'])).
% 8.21/8.44  thf('88', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X0)
% 8.21/8.44          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 8.21/8.44      inference('simplify', [status(thm)], ['87'])).
% 8.21/8.44  thf('89', plain,
% 8.21/8.44      (![X2 : $i, X4 : $i]:
% 8.21/8.44         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 8.21/8.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.21/8.44  thf('90', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 8.21/8.44          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['88', '89'])).
% 8.21/8.44  thf('91', plain,
% 8.21/8.44      ((((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 8.21/8.44        | ~ (v1_relat_1 @ sk_B))),
% 8.21/8.44      inference('sup-', [status(thm)], ['84', '90'])).
% 8.21/8.44  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('93', plain,
% 8.21/8.44      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('demod', [status(thm)], ['91', '92'])).
% 8.21/8.44  thf('94', plain,
% 8.21/8.44      (![X32 : $i, X33 : $i]:
% 8.21/8.44         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 8.21/8.44           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 8.21/8.44          | ~ (v1_relat_1 @ X32))),
% 8.21/8.44      inference('cnf', [status(esa)], [t170_relat_1])).
% 8.21/8.44  thf('95', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 8.21/8.44          | ~ (v1_relat_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['93', '94'])).
% 8.21/8.44  thf('96', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('97', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 8.21/8.44      inference('demod', [status(thm)], ['95', '96'])).
% 8.21/8.44  thf(t146_funct_1, axiom,
% 8.21/8.44    (![A:$i,B:$i]:
% 8.21/8.44     ( ( v1_relat_1 @ B ) =>
% 8.21/8.44       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 8.21/8.44         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 8.21/8.44  thf('98', plain,
% 8.21/8.44      (![X41 : $i, X42 : $i]:
% 8.21/8.44         (~ (r1_tarski @ X41 @ (k1_relat_1 @ X42))
% 8.21/8.44          | (r1_tarski @ X41 @ (k10_relat_1 @ X42 @ (k9_relat_1 @ X42 @ X41)))
% 8.21/8.44          | ~ (v1_relat_1 @ X42))),
% 8.21/8.44      inference('cnf', [status(esa)], [t146_funct_1])).
% 8.21/8.44  thf('99', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ sk_B)
% 8.21/8.44          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ 
% 8.21/8.44             (k10_relat_1 @ sk_B @ 
% 8.21/8.44              (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['97', '98'])).
% 8.21/8.44  thf('100', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('101', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ 
% 8.21/8.44          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))))),
% 8.21/8.44      inference('demod', [status(thm)], ['99', '100'])).
% 8.21/8.44  thf('102', plain,
% 8.21/8.44      (![X5 : $i, X7 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.21/8.44      inference('demod', [status(thm)], ['1', '2'])).
% 8.21/8.44  thf('103', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k6_subset_1 @ (k10_relat_1 @ sk_B @ X0) @ 
% 8.21/8.44           (k10_relat_1 @ sk_B @ 
% 8.21/8.44            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))))
% 8.21/8.44           = (k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['101', '102'])).
% 8.21/8.44  thf('104', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k10_relat_1 @ sk_B @ 
% 8.21/8.44            (k6_subset_1 @ X0 @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))))
% 8.21/8.44            = (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44          | ~ (v1_funct_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['37', '103'])).
% 8.21/8.44  thf('105', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('106', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('107', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k10_relat_1 @ sk_B @ 
% 8.21/8.44           (k6_subset_1 @ X0 @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))))
% 8.21/8.44           = (k1_xboole_0))),
% 8.21/8.44      inference('demod', [status(thm)], ['104', '105', '106'])).
% 8.21/8.44  thf('108', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_funct_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ((k10_relat_1 @ X0 @ (k6_subset_1 @ (k2_relat_1 @ X0) @ X1))
% 8.21/8.44              = (k6_subset_1 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 8.21/8.44      inference('simplify', [status(thm)], ['40'])).
% 8.21/8.44  thf('109', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X1)
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 8.21/8.44              = (k1_xboole_0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['0', '3'])).
% 8.21/8.44  thf('110', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k6_subset_1 @ 
% 8.21/8.44            (k9_relat_1 @ X1 @ 
% 8.21/8.44             (k6_subset_1 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0))) @ 
% 8.21/8.44            (k6_subset_1 @ (k2_relat_1 @ X1) @ X0)) = (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ X1)
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ~ (v1_relat_1 @ X1))),
% 8.21/8.44      inference('sup+', [status(thm)], ['108', '109'])).
% 8.21/8.44  thf('111', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_funct_1 @ X1)
% 8.21/8.44          | ~ (v1_relat_1 @ X1)
% 8.21/8.44          | ((k6_subset_1 @ 
% 8.21/8.44              (k9_relat_1 @ X1 @ 
% 8.21/8.44               (k6_subset_1 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0))) @ 
% 8.21/8.44              (k6_subset_1 @ (k2_relat_1 @ X1) @ X0)) = (k1_xboole_0)))),
% 8.21/8.44      inference('simplify', [status(thm)], ['110'])).
% 8.21/8.44  thf('112', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k6_subset_1 @ 
% 8.21/8.44            (k9_relat_1 @ sk_B @ 
% 8.21/8.44             (k6_subset_1 @ (k1_relat_1 @ sk_B) @ k1_xboole_0)) @ 
% 8.21/8.44            (k6_subset_1 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44             (k6_subset_1 @ X0 @ 
% 8.21/8.44              (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))))
% 8.21/8.44            = (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44          | ~ (v1_funct_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['107', '111'])).
% 8.21/8.44  thf('113', plain, (![X0 : $i]: ((X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['30', '33'])).
% 8.21/8.44  thf('114', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.21/8.44      inference('simplify', [status(thm)], ['11'])).
% 8.21/8.44  thf('115', plain,
% 8.21/8.44      (![X41 : $i, X42 : $i]:
% 8.21/8.44         (~ (r1_tarski @ X41 @ (k1_relat_1 @ X42))
% 8.21/8.44          | (r1_tarski @ X41 @ (k10_relat_1 @ X42 @ (k9_relat_1 @ X42 @ X41)))
% 8.21/8.44          | ~ (v1_relat_1 @ X42))),
% 8.21/8.44      inference('cnf', [status(esa)], [t146_funct_1])).
% 8.21/8.44  thf('116', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X0)
% 8.21/8.44          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 8.21/8.44             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['114', '115'])).
% 8.21/8.44  thf('117', plain,
% 8.21/8.44      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('demod', [status(thm)], ['91', '92'])).
% 8.21/8.44  thf('118', plain,
% 8.21/8.44      (![X32 : $i, X33 : $i]:
% 8.21/8.44         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 8.21/8.44           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 8.21/8.44          | ~ (v1_relat_1 @ X32))),
% 8.21/8.44      inference('cnf', [status(esa)], [t170_relat_1])).
% 8.21/8.44  thf('119', plain,
% 8.21/8.44      (![X2 : $i, X4 : $i]:
% 8.21/8.44         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 8.21/8.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.21/8.44  thf('120', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X0)
% 8.21/8.44          | ~ (r1_tarski @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ 
% 8.21/8.44               (k10_relat_1 @ X0 @ X1))
% 8.21/8.44          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['118', '119'])).
% 8.21/8.44  thf('121', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 8.21/8.44          | ((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))
% 8.21/8.44              = (k10_relat_1 @ sk_B @ X0))
% 8.21/8.44          | ~ (v1_relat_1 @ sk_B))),
% 8.21/8.44      inference('sup-', [status(thm)], ['117', '120'])).
% 8.21/8.44  thf('122', plain,
% 8.21/8.44      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('demod', [status(thm)], ['91', '92'])).
% 8.21/8.44  thf('123', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('124', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 8.21/8.44          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 8.21/8.44      inference('demod', [status(thm)], ['121', '122', '123'])).
% 8.21/8.44  thf('125', plain,
% 8.21/8.44      ((~ (v1_relat_1 @ sk_B)
% 8.21/8.44        | ((k1_relat_1 @ sk_B)
% 8.21/8.44            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['116', '124'])).
% 8.21/8.44  thf('126', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('127', plain,
% 8.21/8.44      (((k1_relat_1 @ sk_B)
% 8.21/8.44         = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 8.21/8.44      inference('demod', [status(thm)], ['125', '126'])).
% 8.21/8.44  thf('128', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_funct_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ((k10_relat_1 @ X0 @ (k6_subset_1 @ (k2_relat_1 @ X0) @ X1))
% 8.21/8.44              = (k6_subset_1 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 8.21/8.44      inference('simplify', [status(thm)], ['40'])).
% 8.21/8.44  thf('129', plain,
% 8.21/8.44      (![X34 : $i, X35 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X34 @ X35) != (k1_xboole_0))
% 8.21/8.44          | (r1_xboole_0 @ (k2_relat_1 @ X34) @ X35)
% 8.21/8.44          | ~ (v1_relat_1 @ X34))),
% 8.21/8.44      inference('cnf', [status(esa)], [t173_relat_1])).
% 8.21/8.44  thf('130', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k6_subset_1 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 8.21/8.44            != (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ X1)
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ~ (v1_relat_1 @ X1)
% 8.21/8.44          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ 
% 8.21/8.44             (k6_subset_1 @ (k2_relat_1 @ X1) @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['128', '129'])).
% 8.21/8.44  thf('131', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r1_xboole_0 @ (k2_relat_1 @ X1) @ 
% 8.21/8.44           (k6_subset_1 @ (k2_relat_1 @ X1) @ X0))
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ~ (v1_relat_1 @ X1)
% 8.21/8.44          | ((k6_subset_1 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 8.21/8.44              != (k1_xboole_0)))),
% 8.21/8.44      inference('simplify', [status(thm)], ['130'])).
% 8.21/8.44  thf('132', plain,
% 8.21/8.44      ((((k6_subset_1 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 8.21/8.44          != (k1_xboole_0))
% 8.21/8.44        | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44        | ~ (v1_funct_1 @ sk_B)
% 8.21/8.44        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44           (k6_subset_1 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44            (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['127', '131'])).
% 8.21/8.44  thf('133', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['12', '13'])).
% 8.21/8.44  thf('134', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('135', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('136', plain,
% 8.21/8.44      ((((k1_xboole_0) != (k1_xboole_0))
% 8.21/8.44        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44           (k6_subset_1 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44            (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))))),
% 8.21/8.44      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 8.21/8.44  thf('137', plain,
% 8.21/8.44      ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44        (k6_subset_1 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44         (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 8.21/8.44      inference('simplify', [status(thm)], ['136'])).
% 8.21/8.44  thf('138', plain,
% 8.21/8.44      (![X15 : $i, X16 : $i]:
% 8.21/8.44         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 8.21/8.44      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.21/8.44  thf('139', plain,
% 8.21/8.44      (![X27 : $i, X28 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 8.21/8.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.21/8.44  thf('140', plain,
% 8.21/8.44      (![X15 : $i, X16 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 8.21/8.44      inference('demod', [status(thm)], ['138', '139'])).
% 8.21/8.44  thf('141', plain,
% 8.21/8.44      (((k6_subset_1 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44         (k6_subset_1 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44          (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))
% 8.21/8.44         = (k2_relat_1 @ sk_B))),
% 8.21/8.44      inference('sup-', [status(thm)], ['137', '140'])).
% 8.21/8.44  thf('142', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf('143', plain,
% 8.21/8.44      (((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44         (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))) = (k2_relat_1 @ sk_B))),
% 8.21/8.44      inference('demod', [status(thm)], ['141', '142'])).
% 8.21/8.44  thf('144', plain,
% 8.21/8.44      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('demod', [status(thm)], ['91', '92'])).
% 8.21/8.44  thf('145', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X1)
% 8.21/8.44          | ~ (v1_funct_1 @ X1)
% 8.21/8.44          | ((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 8.21/8.44              = (k1_xboole_0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['0', '3'])).
% 8.21/8.44  thf('146', plain,
% 8.21/8.44      ((((k6_subset_1 @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) @ 
% 8.21/8.44          (k2_relat_1 @ sk_B)) = (k1_xboole_0))
% 8.21/8.44        | ~ (v1_funct_1 @ sk_B)
% 8.21/8.44        | ~ (v1_relat_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['144', '145'])).
% 8.21/8.44  thf('147', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('148', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('149', plain,
% 8.21/8.44      (((k6_subset_1 @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) @ 
% 8.21/8.44         (k2_relat_1 @ sk_B)) = (k1_xboole_0))),
% 8.21/8.44      inference('demod', [status(thm)], ['146', '147', '148'])).
% 8.21/8.44  thf('150', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf('151', plain,
% 8.21/8.44      (((k6_subset_1 @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) @ k1_xboole_0)
% 8.21/8.44         = (k3_xboole_0 @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) @ 
% 8.21/8.44            (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('sup+', [status(thm)], ['149', '150'])).
% 8.21/8.44  thf('152', plain, (![X0 : $i]: ((X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['30', '33'])).
% 8.21/8.44  thf('153', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.21/8.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.21/8.44  thf('154', plain,
% 8.21/8.44      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))
% 8.21/8.44         = (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44            (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 8.21/8.44      inference('demod', [status(thm)], ['151', '152', '153'])).
% 8.21/8.44  thf('155', plain,
% 8.21/8.44      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['143', '154'])).
% 8.21/8.44  thf('156', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf('157', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('158', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('159', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44           (k6_subset_1 @ X0 @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))))
% 8.21/8.44           = (k1_xboole_0))),
% 8.21/8.44      inference('demod', [status(thm)],
% 8.21/8.44                ['112', '113', '155', '156', '157', '158'])).
% 8.21/8.44  thf('160', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_funct_1 @ X0)
% 8.21/8.44          | ~ (v1_relat_1 @ X0)
% 8.21/8.44          | ((k10_relat_1 @ X0 @ (k6_subset_1 @ X1 @ (k2_relat_1 @ X0)))
% 8.21/8.44              = (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))))),
% 8.21/8.44      inference('simplify', [status(thm)], ['48'])).
% 8.21/8.44  thf('161', plain,
% 8.21/8.44      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('demod', [status(thm)], ['91', '92'])).
% 8.21/8.44  thf('162', plain,
% 8.21/8.44      (![X32 : $i, X33 : $i]:
% 8.21/8.44         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 8.21/8.44           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 8.21/8.44          | ~ (v1_relat_1 @ X32))),
% 8.21/8.44      inference('cnf', [status(esa)], [t170_relat_1])).
% 8.21/8.44  thf('163', plain,
% 8.21/8.44      (![X5 : $i, X7 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 8.21/8.44      inference('demod', [status(thm)], ['1', '2'])).
% 8.21/8.44  thf('164', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v1_relat_1 @ X0)
% 8.21/8.44          | ((k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ 
% 8.21/8.44              (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) = (k1_xboole_0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['162', '163'])).
% 8.21/8.44  thf('165', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k6_subset_1 @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 8.21/8.44            = (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['161', '164'])).
% 8.21/8.44  thf('166', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('167', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k6_subset_1 @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 8.21/8.44           = (k1_xboole_0))),
% 8.21/8.44      inference('demod', [status(thm)], ['165', '166'])).
% 8.21/8.44  thf('168', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf('169', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k6_subset_1 @ (k10_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 8.21/8.44           = (k3_xboole_0 @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B)))),
% 8.21/8.44      inference('sup+', [status(thm)], ['167', '168'])).
% 8.21/8.44  thf('170', plain, (![X0 : $i]: ((X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['30', '33'])).
% 8.21/8.44  thf('171', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.21/8.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.21/8.44  thf('172', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k10_relat_1 @ sk_B @ X0)
% 8.21/8.44           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))),
% 8.21/8.44      inference('demod', [status(thm)], ['169', '170', '171'])).
% 8.21/8.44  thf('173', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 8.21/8.44            = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 8.21/8.44               (k6_subset_1 @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))))
% 8.21/8.44          | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44          | ~ (v1_funct_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['160', '172'])).
% 8.21/8.44  thf('174', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k6_subset_1 @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 8.21/8.44           = (k1_xboole_0))),
% 8.21/8.44      inference('demod', [status(thm)], ['165', '166'])).
% 8.21/8.44  thf('175', plain,
% 8.21/8.44      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['21', '22'])).
% 8.21/8.44  thf('176', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('177', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('178', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k10_relat_1 @ sk_B @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 8.21/8.44           = (k1_xboole_0))),
% 8.21/8.44      inference('demod', [status(thm)], ['173', '174', '175', '176', '177'])).
% 8.21/8.44  thf('179', plain,
% 8.21/8.44      (![X34 : $i, X35 : $i]:
% 8.21/8.44         (((k10_relat_1 @ X34 @ X35) != (k1_xboole_0))
% 8.21/8.44          | (r1_xboole_0 @ (k2_relat_1 @ X34) @ X35)
% 8.21/8.44          | ~ (v1_relat_1 @ X34))),
% 8.21/8.44      inference('cnf', [status(esa)], [t173_relat_1])).
% 8.21/8.44  thf('180', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k1_xboole_0) != (k1_xboole_0))
% 8.21/8.44          | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44          | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44             (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['178', '179'])).
% 8.21/8.44  thf('181', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('182', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((k1_xboole_0) != (k1_xboole_0))
% 8.21/8.44          | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44             (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B))))),
% 8.21/8.44      inference('demod', [status(thm)], ['180', '181'])).
% 8.21/8.44  thf('183', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 8.21/8.44          (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('simplify', [status(thm)], ['182'])).
% 8.21/8.44  thf('184', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf(t63_xboole_1, axiom,
% 8.21/8.44    (![A:$i,B:$i,C:$i]:
% 8.21/8.44     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 8.21/8.44       ( r1_xboole_0 @ A @ C ) ))).
% 8.21/8.44  thf('185', plain,
% 8.21/8.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.21/8.44         (~ (r1_tarski @ X12 @ X13)
% 8.21/8.44          | ~ (r1_xboole_0 @ X13 @ X14)
% 8.21/8.44          | (r1_xboole_0 @ X12 @ X14))),
% 8.21/8.44      inference('cnf', [status(esa)], [t63_xboole_1])).
% 8.21/8.44  thf('186', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r1_xboole_0 @ sk_A @ X0)
% 8.21/8.44          | ~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ X0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['184', '185'])).
% 8.21/8.44  thf('187', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (r1_xboole_0 @ sk_A @ (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['183', '186'])).
% 8.21/8.44  thf('188', plain,
% 8.21/8.44      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 8.21/8.44      inference('demod', [status(thm)], ['15', '16'])).
% 8.21/8.44  thf('189', plain,
% 8.21/8.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.21/8.44         (~ (r1_tarski @ X12 @ X13)
% 8.21/8.44          | ~ (r1_xboole_0 @ X13 @ X14)
% 8.21/8.44          | (r1_xboole_0 @ X12 @ X14))),
% 8.21/8.44      inference('cnf', [status(esa)], [t63_xboole_1])).
% 8.21/8.44  thf('190', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((r1_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 8.21/8.44          | ~ (r1_xboole_0 @ X0 @ X2))),
% 8.21/8.44      inference('sup-', [status(thm)], ['188', '189'])).
% 8.21/8.44  thf('191', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (r1_xboole_0 @ (k6_subset_1 @ sk_A @ X1) @ 
% 8.21/8.44          (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['187', '190'])).
% 8.21/8.44  thf('192', plain,
% 8.21/8.44      (![X15 : $i, X16 : $i]:
% 8.21/8.44         (((k6_subset_1 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 8.21/8.44      inference('demod', [status(thm)], ['138', '139'])).
% 8.21/8.44  thf('193', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((k6_subset_1 @ (k6_subset_1 @ sk_A @ X1) @ 
% 8.21/8.44           (k6_subset_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 8.21/8.44           = (k6_subset_1 @ sk_A @ X1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['191', '192'])).
% 8.21/8.44  thf('194', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf('195', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k6_subset_1 @ sk_A @ X0)
% 8.21/8.44           = (k3_xboole_0 @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_B)))),
% 8.21/8.44      inference('sup+', [status(thm)], ['193', '194'])).
% 8.21/8.44  thf('196', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.21/8.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.21/8.44  thf('197', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k6_subset_1 @ sk_A @ X0))
% 8.21/8.44           = (k6_subset_1 @ sk_A @ X0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['195', '196'])).
% 8.21/8.44  thf('198', plain,
% 8.21/8.44      (((k1_xboole_0)
% 8.21/8.44         = (k6_subset_1 @ sk_A @ 
% 8.21/8.44            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 8.21/8.44      inference('sup+', [status(thm)], ['159', '197'])).
% 8.21/8.44  thf('199', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 8.21/8.44           = (k3_xboole_0 @ X10 @ X11))),
% 8.21/8.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.21/8.44  thf('200', plain,
% 8.21/8.44      (((k6_subset_1 @ sk_A @ k1_xboole_0)
% 8.21/8.44         = (k3_xboole_0 @ sk_A @ 
% 8.21/8.44            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 8.21/8.44      inference('sup+', [status(thm)], ['198', '199'])).
% 8.21/8.44  thf('201', plain, (![X0 : $i]: ((X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['30', '33'])).
% 8.21/8.44  thf('202', plain,
% 8.21/8.44      (((sk_A)
% 8.21/8.44         = (k3_xboole_0 @ sk_A @ 
% 8.21/8.44            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 8.21/8.44      inference('demod', [status(thm)], ['200', '201'])).
% 8.21/8.44  thf('203', plain,
% 8.21/8.44      ((((sk_A) = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 8.21/8.44        | ~ (v1_relat_1 @ sk_B)
% 8.21/8.44        | ~ (v1_funct_1 @ sk_B))),
% 8.21/8.44      inference('sup+', [status(thm)], ['36', '202'])).
% 8.21/8.44  thf('204', plain, ((v1_relat_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('205', plain, ((v1_funct_1 @ sk_B)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('206', plain,
% 8.21/8.44      (((sk_A) = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 8.21/8.44      inference('demod', [status(thm)], ['203', '204', '205'])).
% 8.21/8.44  thf('207', plain,
% 8.21/8.44      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('208', plain, ($false),
% 8.21/8.44      inference('simplify_reflect-', [status(thm)], ['206', '207'])).
% 8.21/8.44  
% 8.21/8.44  % SZS output end Refutation
% 8.21/8.44  
% 8.21/8.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
