%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yWCGuM1m5Z

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:38 EST 2020

% Result     : Theorem 27.50s
% Output     : Refutation 27.50s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 193 expanded)
%              Number of leaves         :   23 (  67 expanded)
%              Depth                    :   25
%              Number of atoms          :  994 (1720 expanded)
%              Number of equality atoms :   55 ( 121 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ ( k6_subset_1 @ X15 @ X16 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X14 @ X15 ) @ ( k9_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
        = ( k4_xboole_0 @ ( k9_relat_1 @ X14 @ X15 ) @ ( k9_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X20 @ ( k10_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k4_xboole_0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X12 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( r1_tarski @ X22 @ ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X17 @ X18 ) @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X17 @ X18 ) @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ X1 )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('33',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X17 @ X18 ) @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X17 @ X18 ) @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ ( k10_relat_1 @ X2 @ k1_xboole_0 ) @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ ( k10_relat_1 @ X2 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf(t152_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_funct_1])).

thf('75',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['76','77','78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yWCGuM1m5Z
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 27.50/27.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 27.50/27.74  % Solved by: fo/fo7.sh
% 27.50/27.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.50/27.74  % done 20552 iterations in 27.309s
% 27.50/27.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 27.50/27.74  % SZS output start Refutation
% 27.50/27.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 27.50/27.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 27.50/27.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 27.50/27.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 27.50/27.74  thf(sk_B_type, type, sk_B: $i).
% 27.50/27.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 27.50/27.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.50/27.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 27.50/27.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 27.50/27.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 27.50/27.74  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 27.50/27.74  thf(sk_A_type, type, sk_A: $i).
% 27.50/27.74  thf(t123_funct_1, axiom,
% 27.50/27.74    (![A:$i,B:$i,C:$i]:
% 27.50/27.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 27.50/27.74       ( ( v2_funct_1 @ C ) =>
% 27.50/27.74         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 27.50/27.74           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 27.50/27.74  thf('0', plain,
% 27.50/27.74      (![X14 : $i, X15 : $i, X16 : $i]:
% 27.50/27.74         (~ (v2_funct_1 @ X14)
% 27.50/27.74          | ((k9_relat_1 @ X14 @ (k6_subset_1 @ X15 @ X16))
% 27.50/27.74              = (k6_subset_1 @ (k9_relat_1 @ X14 @ X15) @ 
% 27.50/27.74                 (k9_relat_1 @ X14 @ X16)))
% 27.50/27.74          | ~ (v1_funct_1 @ X14)
% 27.50/27.74          | ~ (v1_relat_1 @ X14))),
% 27.50/27.74      inference('cnf', [status(esa)], [t123_funct_1])).
% 27.50/27.74  thf(redefinition_k6_subset_1, axiom,
% 27.50/27.74    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 27.50/27.74  thf('1', plain,
% 27.50/27.74      (![X10 : $i, X11 : $i]:
% 27.50/27.74         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 27.50/27.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.50/27.74  thf('2', plain,
% 27.50/27.74      (![X10 : $i, X11 : $i]:
% 27.50/27.74         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 27.50/27.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.50/27.74  thf('3', plain,
% 27.50/27.74      (![X14 : $i, X15 : $i, X16 : $i]:
% 27.50/27.74         (~ (v2_funct_1 @ X14)
% 27.50/27.74          | ((k9_relat_1 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 27.50/27.74              = (k4_xboole_0 @ (k9_relat_1 @ X14 @ X15) @ 
% 27.50/27.74                 (k9_relat_1 @ X14 @ X16)))
% 27.50/27.74          | ~ (v1_funct_1 @ X14)
% 27.50/27.74          | ~ (v1_relat_1 @ X14))),
% 27.50/27.74      inference('demod', [status(thm)], ['0', '1', '2'])).
% 27.50/27.74  thf(t145_funct_1, axiom,
% 27.50/27.74    (![A:$i,B:$i]:
% 27.50/27.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 27.50/27.74       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 27.50/27.74  thf('4', plain,
% 27.50/27.74      (![X20 : $i, X21 : $i]:
% 27.50/27.74         ((r1_tarski @ (k9_relat_1 @ X20 @ (k10_relat_1 @ X20 @ X21)) @ X21)
% 27.50/27.74          | ~ (v1_funct_1 @ X20)
% 27.50/27.74          | ~ (v1_relat_1 @ X20))),
% 27.50/27.74      inference('cnf', [status(esa)], [t145_funct_1])).
% 27.50/27.74  thf(l32_xboole_1, axiom,
% 27.50/27.74    (![A:$i,B:$i]:
% 27.50/27.74     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 27.50/27.74  thf('5', plain,
% 27.50/27.74      (![X3 : $i, X5 : $i]:
% 27.50/27.74         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 27.50/27.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.50/27.74  thf('6', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ((k4_xboole_0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 27.50/27.74              = (k1_xboole_0)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['4', '5'])).
% 27.50/27.74  thf('7', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((k9_relat_1 @ X1 @ 
% 27.50/27.74            (k4_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 27.50/27.74            = (k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v2_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1))),
% 27.50/27.74      inference('sup+', [status(thm)], ['3', '6'])).
% 27.50/27.74  thf('8', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (v2_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | ((k9_relat_1 @ X1 @ 
% 27.50/27.74              (k4_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 27.50/27.74              = (k1_xboole_0)))),
% 27.50/27.74      inference('simplify', [status(thm)], ['7'])).
% 27.50/27.74  thf(t167_relat_1, axiom,
% 27.50/27.74    (![A:$i,B:$i]:
% 27.50/27.74     ( ( v1_relat_1 @ B ) =>
% 27.50/27.74       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 27.50/27.74  thf('9', plain,
% 27.50/27.74      (![X12 : $i, X13 : $i]:
% 27.50/27.74         ((r1_tarski @ (k10_relat_1 @ X12 @ X13) @ (k1_relat_1 @ X12))
% 27.50/27.74          | ~ (v1_relat_1 @ X12))),
% 27.50/27.74      inference('cnf', [status(esa)], [t167_relat_1])).
% 27.50/27.74  thf(t109_xboole_1, axiom,
% 27.50/27.74    (![A:$i,B:$i,C:$i]:
% 27.50/27.74     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 27.50/27.74  thf('10', plain,
% 27.50/27.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 27.50/27.74         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 27.50/27.74      inference('cnf', [status(esa)], [t109_xboole_1])).
% 27.50/27.74  thf('11', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.50/27.74         (~ (v1_relat_1 @ X0)
% 27.50/27.74          | (r1_tarski @ (k4_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 27.50/27.74             (k1_relat_1 @ X0)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['9', '10'])).
% 27.50/27.74  thf(t146_funct_1, axiom,
% 27.50/27.74    (![A:$i,B:$i]:
% 27.50/27.74     ( ( v1_relat_1 @ B ) =>
% 27.50/27.74       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 27.50/27.74         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 27.50/27.74  thf('12', plain,
% 27.50/27.74      (![X22 : $i, X23 : $i]:
% 27.50/27.74         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 27.50/27.74          | (r1_tarski @ X22 @ (k10_relat_1 @ X23 @ (k9_relat_1 @ X23 @ X22)))
% 27.50/27.74          | ~ (v1_relat_1 @ X23))),
% 27.50/27.74      inference('cnf', [status(esa)], [t146_funct_1])).
% 27.50/27.74  thf('13', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.50/27.74         (~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | (r1_tarski @ (k4_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1) @ 
% 27.50/27.74             (k10_relat_1 @ X0 @ 
% 27.50/27.74              (k9_relat_1 @ X0 @ (k4_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1)))))),
% 27.50/27.74      inference('sup-', [status(thm)], ['11', '12'])).
% 27.50/27.74  thf('14', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.50/27.74         ((r1_tarski @ (k4_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1) @ 
% 27.50/27.74           (k10_relat_1 @ X0 @ 
% 27.50/27.74            (k9_relat_1 @ X0 @ (k4_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1))))
% 27.50/27.74          | ~ (v1_relat_1 @ X0))),
% 27.50/27.74      inference('simplify', [status(thm)], ['13'])).
% 27.50/27.74  thf('15', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         ((r1_tarski @ 
% 27.50/27.74           (k4_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0) @ 
% 27.50/27.74           (k10_relat_1 @ X1 @ k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v2_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1))),
% 27.50/27.74      inference('sup+', [status(thm)], ['8', '14'])).
% 27.50/27.74  thf('16', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (v2_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | (r1_tarski @ 
% 27.50/27.74             (k4_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0) @ 
% 27.50/27.74             (k10_relat_1 @ X1 @ k1_xboole_0)))),
% 27.50/27.74      inference('simplify', [status(thm)], ['15'])).
% 27.50/27.74  thf(t3_boole, axiom,
% 27.50/27.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 27.50/27.74  thf('17', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 27.50/27.74      inference('cnf', [status(esa)], [t3_boole])).
% 27.50/27.74  thf(t138_funct_1, axiom,
% 27.50/27.74    (![A:$i,B:$i,C:$i]:
% 27.50/27.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 27.50/27.74       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 27.50/27.74         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 27.50/27.74  thf('18', plain,
% 27.50/27.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19))
% 27.50/27.74            = (k6_subset_1 @ (k10_relat_1 @ X17 @ X18) @ 
% 27.50/27.74               (k10_relat_1 @ X17 @ X19)))
% 27.50/27.74          | ~ (v1_funct_1 @ X17)
% 27.50/27.74          | ~ (v1_relat_1 @ X17))),
% 27.50/27.74      inference('cnf', [status(esa)], [t138_funct_1])).
% 27.50/27.74  thf('19', plain,
% 27.50/27.74      (![X10 : $i, X11 : $i]:
% 27.50/27.74         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 27.50/27.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.50/27.74  thf('20', plain,
% 27.50/27.74      (![X10 : $i, X11 : $i]:
% 27.50/27.74         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 27.50/27.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.50/27.74  thf('21', plain,
% 27.50/27.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 27.50/27.74            = (k4_xboole_0 @ (k10_relat_1 @ X17 @ X18) @ 
% 27.50/27.74               (k10_relat_1 @ X17 @ X19)))
% 27.50/27.74          | ~ (v1_funct_1 @ X17)
% 27.50/27.74          | ~ (v1_relat_1 @ X17))),
% 27.50/27.74      inference('demod', [status(thm)], ['18', '19', '20'])).
% 27.50/27.74  thf(d10_xboole_0, axiom,
% 27.50/27.74    (![A:$i,B:$i]:
% 27.50/27.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.50/27.74  thf('22', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 27.50/27.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.50/27.74  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 27.50/27.74      inference('simplify', [status(thm)], ['22'])).
% 27.50/27.74  thf('24', plain,
% 27.50/27.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 27.50/27.74         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 27.50/27.74      inference('cnf', [status(esa)], [t109_xboole_1])).
% 27.50/27.74  thf('25', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 27.50/27.74      inference('sup-', [status(thm)], ['23', '24'])).
% 27.50/27.74  thf('26', plain,
% 27.50/27.74      (![X0 : $i, X2 : $i]:
% 27.50/27.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 27.50/27.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.50/27.74  thf('27', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 27.50/27.74          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['25', '26'])).
% 27.50/27.74  thf('28', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.50/27.74         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 27.50/27.74             (k10_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 27.50/27.74          | ~ (v1_relat_1 @ X2)
% 27.50/27.74          | ~ (v1_funct_1 @ X2)
% 27.50/27.74          | ((k10_relat_1 @ X2 @ X1)
% 27.50/27.74              = (k4_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ 
% 27.50/27.74                 (k10_relat_1 @ X2 @ X0))))),
% 27.50/27.74      inference('sup-', [status(thm)], ['21', '27'])).
% 27.50/27.74  thf('29', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (r1_tarski @ (k10_relat_1 @ X1 @ X0) @ (k10_relat_1 @ X1 @ X0))
% 27.50/27.74          | ((k10_relat_1 @ X1 @ X0)
% 27.50/27.74              = (k4_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ 
% 27.50/27.74                 (k10_relat_1 @ X1 @ k1_xboole_0)))
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1))),
% 27.50/27.74      inference('sup-', [status(thm)], ['17', '28'])).
% 27.50/27.74  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 27.50/27.74      inference('simplify', [status(thm)], ['22'])).
% 27.50/27.74  thf('31', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X1 @ X0)
% 27.50/27.74            = (k4_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ 
% 27.50/27.74               (k10_relat_1 @ X1 @ k1_xboole_0)))
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1))),
% 27.50/27.74      inference('demod', [status(thm)], ['29', '30'])).
% 27.50/27.74  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 27.50/27.74      inference('simplify', [status(thm)], ['22'])).
% 27.50/27.74  thf('33', plain,
% 27.50/27.74      (![X3 : $i, X5 : $i]:
% 27.50/27.74         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 27.50/27.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.50/27.74  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['32', '33'])).
% 27.50/27.74  thf('35', plain,
% 27.50/27.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 27.50/27.74            = (k4_xboole_0 @ (k10_relat_1 @ X17 @ X18) @ 
% 27.50/27.74               (k10_relat_1 @ X17 @ X19)))
% 27.50/27.74          | ~ (v1_funct_1 @ X17)
% 27.50/27.74          | ~ (v1_relat_1 @ X17))),
% 27.50/27.74      inference('demod', [status(thm)], ['18', '19', '20'])).
% 27.50/27.74  thf('36', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1))),
% 27.50/27.74      inference('sup+', [status(thm)], ['34', '35'])).
% 27.50/27.74  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['32', '33'])).
% 27.50/27.74  thf('38', plain,
% 27.50/27.74      (![X1 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1))),
% 27.50/27.74      inference('demod', [status(thm)], ['36', '37'])).
% 27.50/27.74  thf('39', plain,
% 27.50/27.74      (![X1 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1))),
% 27.50/27.74      inference('demod', [status(thm)], ['36', '37'])).
% 27.50/27.74  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['32', '33'])).
% 27.50/27.74  thf('41', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 27.50/27.74      inference('sup-', [status(thm)], ['23', '24'])).
% 27.50/27.74  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 27.50/27.74      inference('sup+', [status(thm)], ['40', '41'])).
% 27.50/27.74  thf('43', plain,
% 27.50/27.74      (![X3 : $i, X5 : $i]:
% 27.50/27.74         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 27.50/27.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.50/27.74  thf('44', plain,
% 27.50/27.74      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['42', '43'])).
% 27.50/27.74  thf('45', plain,
% 27.50/27.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 27.50/27.74            = (k4_xboole_0 @ (k10_relat_1 @ X17 @ X18) @ 
% 27.50/27.74               (k10_relat_1 @ X17 @ X19)))
% 27.50/27.74          | ~ (v1_funct_1 @ X17)
% 27.50/27.74          | ~ (v1_relat_1 @ X17))),
% 27.50/27.74      inference('demod', [status(thm)], ['18', '19', '20'])).
% 27.50/27.74  thf('46', plain,
% 27.50/27.74      (![X3 : $i, X4 : $i]:
% 27.50/27.74         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 27.50/27.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.50/27.74  thf('47', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X2)
% 27.50/27.74          | ~ (v1_funct_1 @ X2)
% 27.50/27.74          | (r1_tarski @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['45', '46'])).
% 27.50/27.74  thf('48', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((k10_relat_1 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 27.50/27.74          | (r1_tarski @ (k10_relat_1 @ X1 @ k1_xboole_0) @ 
% 27.50/27.74             (k10_relat_1 @ X1 @ X0))
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1))),
% 27.50/27.74      inference('sup-', [status(thm)], ['44', '47'])).
% 27.50/27.74  thf('49', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((k1_xboole_0) != (k1_xboole_0))
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | (r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ 
% 27.50/27.74             (k10_relat_1 @ X0 @ X1)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['39', '48'])).
% 27.50/27.74  thf('50', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         ((r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ 
% 27.50/27.74           (k10_relat_1 @ X0 @ X1))
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0))),
% 27.50/27.74      inference('simplify', [status(thm)], ['49'])).
% 27.50/27.74  thf('51', plain,
% 27.50/27.74      (![X0 : $i]:
% 27.50/27.74         ((r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0))),
% 27.50/27.74      inference('sup+', [status(thm)], ['38', '50'])).
% 27.50/27.74  thf('52', plain,
% 27.50/27.74      (![X0 : $i]:
% 27.50/27.74         (~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | (r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 27.50/27.74      inference('simplify', [status(thm)], ['51'])).
% 27.50/27.74  thf('53', plain,
% 27.50/27.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 27.50/27.74         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 27.50/27.74      inference('cnf', [status(esa)], [t109_xboole_1])).
% 27.50/27.74  thf('54', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | (r1_tarski @ 
% 27.50/27.74             (k4_xboole_0 @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1) @ 
% 27.50/27.74             k1_xboole_0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['52', '53'])).
% 27.50/27.74  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 27.50/27.74      inference('sup+', [status(thm)], ['40', '41'])).
% 27.50/27.74  thf('56', plain,
% 27.50/27.74      (![X0 : $i, X2 : $i]:
% 27.50/27.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 27.50/27.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.50/27.74  thf('57', plain,
% 27.50/27.74      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['55', '56'])).
% 27.50/27.74  thf('58', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ((k4_xboole_0 @ (k10_relat_1 @ X1 @ k1_xboole_0) @ X0)
% 27.50/27.74              = (k1_xboole_0)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['54', '57'])).
% 27.50/27.74  thf('59', plain,
% 27.50/27.74      (![X3 : $i, X4 : $i]:
% 27.50/27.74         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 27.50/27.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.50/27.74  thf('60', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((k1_xboole_0) != (k1_xboole_0))
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | (r1_tarski @ (k10_relat_1 @ X1 @ k1_xboole_0) @ X0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['58', '59'])).
% 27.50/27.74  thf('61', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         ((r1_tarski @ (k10_relat_1 @ X1 @ k1_xboole_0) @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1))),
% 27.50/27.74      inference('simplify', [status(thm)], ['60'])).
% 27.50/27.74  thf('62', plain,
% 27.50/27.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 27.50/27.74         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 27.50/27.74      inference('cnf', [status(esa)], [t109_xboole_1])).
% 27.50/27.74  thf('63', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.50/27.74         (~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | (r1_tarski @ 
% 27.50/27.74             (k4_xboole_0 @ (k10_relat_1 @ X1 @ k1_xboole_0) @ X2) @ X0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['61', '62'])).
% 27.50/27.74  thf('64', plain,
% 27.50/27.74      (![X0 : $i, X2 : $i]:
% 27.50/27.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 27.50/27.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.50/27.74  thf('65', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.50/27.74         (~ (v1_relat_1 @ X2)
% 27.50/27.74          | ~ (v1_funct_1 @ X2)
% 27.50/27.74          | ~ (r1_tarski @ X0 @ 
% 27.50/27.74               (k4_xboole_0 @ (k10_relat_1 @ X2 @ k1_xboole_0) @ X1))
% 27.50/27.74          | ((X0) = (k4_xboole_0 @ (k10_relat_1 @ X2 @ k1_xboole_0) @ X1)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['63', '64'])).
% 27.50/27.74  thf('66', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (r1_tarski @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ((X1)
% 27.50/27.74              = (k4_xboole_0 @ (k10_relat_1 @ X0 @ k1_xboole_0) @ 
% 27.50/27.74                 (k10_relat_1 @ X0 @ k1_xboole_0)))
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['31', '65'])).
% 27.50/27.74  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['32', '33'])).
% 27.50/27.74  thf('68', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (r1_tarski @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ((X1) = (k1_xboole_0))
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0))),
% 27.50/27.74      inference('demod', [status(thm)], ['66', '67'])).
% 27.50/27.74  thf('69', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((X1) = (k1_xboole_0))
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (r1_tarski @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 27.50/27.74      inference('simplify', [status(thm)], ['68'])).
% 27.50/27.74  thf('70', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v2_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ((k4_xboole_0 @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 27.50/27.74              = (k1_xboole_0)))),
% 27.50/27.74      inference('sup-', [status(thm)], ['16', '69'])).
% 27.50/27.74  thf('71', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((k4_xboole_0 @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 27.50/27.74            = (k1_xboole_0))
% 27.50/27.74          | ~ (v2_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_funct_1 @ X0)
% 27.50/27.74          | ~ (v1_relat_1 @ X0))),
% 27.50/27.74      inference('simplify', [status(thm)], ['70'])).
% 27.50/27.74  thf('72', plain,
% 27.50/27.74      (![X3 : $i, X4 : $i]:
% 27.50/27.74         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 27.50/27.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 27.50/27.74  thf('73', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         (((k1_xboole_0) != (k1_xboole_0))
% 27.50/27.74          | ~ (v1_relat_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v2_funct_1 @ X1)
% 27.50/27.74          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 27.50/27.74      inference('sup-', [status(thm)], ['71', '72'])).
% 27.50/27.74  thf('74', plain,
% 27.50/27.74      (![X0 : $i, X1 : $i]:
% 27.50/27.74         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 27.50/27.74          | ~ (v2_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_funct_1 @ X1)
% 27.50/27.74          | ~ (v1_relat_1 @ X1))),
% 27.50/27.74      inference('simplify', [status(thm)], ['73'])).
% 27.50/27.74  thf(t152_funct_1, conjecture,
% 27.50/27.74    (![A:$i,B:$i]:
% 27.50/27.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 27.50/27.74       ( ( v2_funct_1 @ B ) =>
% 27.50/27.74         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 27.50/27.74  thf(zf_stmt_0, negated_conjecture,
% 27.50/27.74    (~( ![A:$i,B:$i]:
% 27.50/27.74        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 27.50/27.74          ( ( v2_funct_1 @ B ) =>
% 27.50/27.74            ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )),
% 27.50/27.74    inference('cnf.neg', [status(esa)], [t152_funct_1])).
% 27.50/27.74  thf('75', plain,
% 27.50/27.74      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 27.50/27.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.50/27.74  thf('76', plain,
% 27.50/27.74      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 27.50/27.74      inference('sup-', [status(thm)], ['74', '75'])).
% 27.50/27.74  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 27.50/27.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.50/27.74  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 27.50/27.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.50/27.74  thf('79', plain, ((v2_funct_1 @ sk_B)),
% 27.50/27.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.50/27.74  thf('80', plain, ($false),
% 27.50/27.74      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 27.50/27.74  
% 27.50/27.74  % SZS output end Refutation
% 27.50/27.74  
% 27.57/27.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
