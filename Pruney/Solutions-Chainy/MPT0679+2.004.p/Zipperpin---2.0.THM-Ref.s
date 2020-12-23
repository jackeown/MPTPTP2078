%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8fRkG7d7vH

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:02 EST 2020

% Result     : Theorem 18.69s
% Output     : Refutation 18.69s
% Verified   : 
% Statistics : Number of formulae       :   69 (  81 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  640 ( 799 expanded)
%              Number of equality atoms :   31 (  43 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X6 @ X7 ) @ X6 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t158_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k9_relat_1 @ X21 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t158_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) @ X14 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k6_subset_1 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X13 @ X14 ) @ X14 ) ),
    inference(demod,[status(thm)],['10','11','15'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k9_relat_1 @ X25 @ ( k3_xboole_0 @ X26 @ X27 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X25 @ X26 ) @ ( k9_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ ( k6_subset_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ ( k6_subset_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k6_subset_1 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k6_subset_1 @ X2 @ X0 ) ) @ ( k6_subset_1 @ X3 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k6_subset_1 @ X2 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X2 ) ) @ ( k6_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X2 ) ) @ ( k6_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t155_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ X18 @ X19 ) @ ( k9_relat_1 @ X18 @ X20 ) ) @ ( k9_relat_1 @ X18 @ ( k6_subset_1 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t155_relat_1])).

thf('32',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k6_subset_1 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) )
      | ( ( k9_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k6_subset_1 @ X2 @ X0 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k6_subset_1 @ X2 @ X0 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t123_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( v2_funct_1 @ C )
         => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t123_funct_1])).

thf('36',plain,(
    ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
 != ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
     != ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8fRkG7d7vH
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.69/18.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.69/18.90  % Solved by: fo/fo7.sh
% 18.69/18.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.69/18.90  % done 6115 iterations in 18.411s
% 18.69/18.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.69/18.90  % SZS output start Refutation
% 18.69/18.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 18.69/18.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 18.69/18.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 18.69/18.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.69/18.90  thf(sk_B_type, type, sk_B: $i).
% 18.69/18.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 18.69/18.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.69/18.90  thf(sk_C_type, type, sk_C: $i).
% 18.69/18.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 18.69/18.90  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 18.69/18.90  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 18.69/18.90  thf(sk_A_type, type, sk_A: $i).
% 18.69/18.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 18.69/18.90  thf(t36_xboole_1, axiom,
% 18.69/18.90    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 18.69/18.90  thf('0', plain,
% 18.69/18.90      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 18.69/18.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 18.69/18.90  thf(redefinition_k6_subset_1, axiom,
% 18.69/18.90    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 18.69/18.90  thf('1', plain,
% 18.69/18.90      (![X15 : $i, X16 : $i]:
% 18.69/18.90         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 18.69/18.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.69/18.90  thf('2', plain,
% 18.69/18.90      (![X6 : $i, X7 : $i]: (r1_tarski @ (k6_subset_1 @ X6 @ X7) @ X6)),
% 18.69/18.90      inference('demod', [status(thm)], ['0', '1'])).
% 18.69/18.90  thf(d10_xboole_0, axiom,
% 18.69/18.90    (![A:$i,B:$i]:
% 18.69/18.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 18.69/18.90  thf('3', plain,
% 18.69/18.90      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 18.69/18.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 18.69/18.90  thf('4', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 18.69/18.90      inference('simplify', [status(thm)], ['3'])).
% 18.69/18.90  thf(t158_relat_1, axiom,
% 18.69/18.90    (![A:$i,B:$i,C:$i]:
% 18.69/18.90     ( ( v1_relat_1 @ C ) =>
% 18.69/18.90       ( ![D:$i]:
% 18.69/18.90         ( ( v1_relat_1 @ D ) =>
% 18.69/18.90           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 18.69/18.90             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 18.69/18.90  thf('5', plain,
% 18.69/18.90      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 18.69/18.90         (~ (v1_relat_1 @ X21)
% 18.69/18.90          | (r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k9_relat_1 @ X21 @ X24))
% 18.69/18.90          | ~ (r1_tarski @ X22 @ X21)
% 18.69/18.90          | ~ (r1_tarski @ X23 @ X24)
% 18.69/18.90          | ~ (v1_relat_1 @ X22))),
% 18.69/18.90      inference('cnf', [status(esa)], [t158_relat_1])).
% 18.69/18.90  thf('6', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (~ (v1_relat_1 @ X0)
% 18.69/18.90          | ~ (r1_tarski @ X2 @ X1)
% 18.69/18.90          | (r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 18.69/18.90          | ~ (v1_relat_1 @ X0))),
% 18.69/18.90      inference('sup-', [status(thm)], ['4', '5'])).
% 18.69/18.90  thf('7', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         ((r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 18.69/18.90          | ~ (r1_tarski @ X2 @ X1)
% 18.69/18.90          | ~ (v1_relat_1 @ X0))),
% 18.69/18.90      inference('simplify', [status(thm)], ['6'])).
% 18.69/18.90  thf('8', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (~ (v1_relat_1 @ X2)
% 18.69/18.90          | (r1_tarski @ (k9_relat_1 @ X2 @ (k6_subset_1 @ X0 @ X1)) @ 
% 18.69/18.90             (k9_relat_1 @ X2 @ X0)))),
% 18.69/18.90      inference('sup-', [status(thm)], ['2', '7'])).
% 18.69/18.90  thf(t149_relat_1, axiom,
% 18.69/18.90    (![A:$i]:
% 18.69/18.90     ( ( v1_relat_1 @ A ) =>
% 18.69/18.90       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 18.69/18.90  thf('9', plain,
% 18.69/18.90      (![X17 : $i]:
% 18.69/18.90         (((k9_relat_1 @ X17 @ k1_xboole_0) = (k1_xboole_0))
% 18.69/18.90          | ~ (v1_relat_1 @ X17))),
% 18.69/18.90      inference('cnf', [status(esa)], [t149_relat_1])).
% 18.69/18.90  thf(t90_xboole_1, axiom,
% 18.69/18.90    (![A:$i,B:$i]:
% 18.69/18.90     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 18.69/18.90  thf('10', plain,
% 18.69/18.90      (![X13 : $i, X14 : $i]:
% 18.69/18.90         (r1_xboole_0 @ (k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)) @ X14)),
% 18.69/18.90      inference('cnf', [status(esa)], [t90_xboole_1])).
% 18.69/18.90  thf('11', plain,
% 18.69/18.90      (![X15 : $i, X16 : $i]:
% 18.69/18.90         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 18.69/18.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.69/18.90  thf(t47_xboole_1, axiom,
% 18.69/18.90    (![A:$i,B:$i]:
% 18.69/18.90     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 18.69/18.90  thf('12', plain,
% 18.69/18.90      (![X8 : $i, X9 : $i]:
% 18.69/18.90         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 18.69/18.90           = (k4_xboole_0 @ X8 @ X9))),
% 18.69/18.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 18.69/18.90  thf('13', plain,
% 18.69/18.90      (![X15 : $i, X16 : $i]:
% 18.69/18.90         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 18.69/18.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.69/18.90  thf('14', plain,
% 18.69/18.90      (![X15 : $i, X16 : $i]:
% 18.69/18.90         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 18.69/18.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.69/18.90  thf('15', plain,
% 18.69/18.90      (![X8 : $i, X9 : $i]:
% 18.69/18.90         ((k6_subset_1 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 18.69/18.90           = (k6_subset_1 @ X8 @ X9))),
% 18.69/18.90      inference('demod', [status(thm)], ['12', '13', '14'])).
% 18.69/18.90  thf('16', plain,
% 18.69/18.90      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X13 @ X14) @ X14)),
% 18.69/18.90      inference('demod', [status(thm)], ['10', '11', '15'])).
% 18.69/18.90  thf(d7_xboole_0, axiom,
% 18.69/18.90    (![A:$i,B:$i]:
% 18.69/18.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 18.69/18.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 18.69/18.90  thf('17', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i]:
% 18.69/18.90         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 18.69/18.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 18.69/18.90  thf('18', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i]:
% 18.69/18.90         ((k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 18.69/18.90      inference('sup-', [status(thm)], ['16', '17'])).
% 18.69/18.90  thf(t121_funct_1, axiom,
% 18.69/18.90    (![A:$i,B:$i,C:$i]:
% 18.69/18.90     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 18.69/18.90       ( ( v2_funct_1 @ C ) =>
% 18.69/18.90         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 18.69/18.90           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 18.69/18.90  thf('19', plain,
% 18.69/18.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 18.69/18.90         (~ (v2_funct_1 @ X25)
% 18.69/18.90          | ((k9_relat_1 @ X25 @ (k3_xboole_0 @ X26 @ X27))
% 18.69/18.90              = (k3_xboole_0 @ (k9_relat_1 @ X25 @ X26) @ 
% 18.69/18.90                 (k9_relat_1 @ X25 @ X27)))
% 18.69/18.90          | ~ (v1_funct_1 @ X25)
% 18.69/18.90          | ~ (v1_relat_1 @ X25))),
% 18.69/18.90      inference('cnf', [status(esa)], [t121_funct_1])).
% 18.69/18.90  thf('20', plain,
% 18.69/18.90      (![X0 : $i, X2 : $i]:
% 18.69/18.90         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 18.69/18.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 18.69/18.90  thf('21', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 18.69/18.90          | ~ (v1_relat_1 @ X2)
% 18.69/18.90          | ~ (v1_funct_1 @ X2)
% 18.69/18.90          | ~ (v2_funct_1 @ X2)
% 18.69/18.90          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 18.69/18.90      inference('sup-', [status(thm)], ['19', '20'])).
% 18.69/18.90  thf('22', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (((k9_relat_1 @ X2 @ k1_xboole_0) != (k1_xboole_0))
% 18.69/18.90          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)) @ 
% 18.69/18.90             (k9_relat_1 @ X2 @ X0))
% 18.69/18.90          | ~ (v2_funct_1 @ X2)
% 18.69/18.90          | ~ (v1_funct_1 @ X2)
% 18.69/18.90          | ~ (v1_relat_1 @ X2))),
% 18.69/18.90      inference('sup-', [status(thm)], ['18', '21'])).
% 18.69/18.90  thf('23', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (((k1_xboole_0) != (k1_xboole_0))
% 18.69/18.90          | ~ (v1_relat_1 @ X0)
% 18.69/18.90          | ~ (v1_relat_1 @ X0)
% 18.69/18.90          | ~ (v1_funct_1 @ X0)
% 18.69/18.90          | ~ (v2_funct_1 @ X0)
% 18.69/18.90          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ (k6_subset_1 @ X2 @ X1)) @ 
% 18.69/18.90             (k9_relat_1 @ X0 @ X1)))),
% 18.69/18.90      inference('sup-', [status(thm)], ['9', '22'])).
% 18.69/18.90  thf('24', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ (k6_subset_1 @ X2 @ X1)) @ 
% 18.69/18.90           (k9_relat_1 @ X0 @ X1))
% 18.69/18.90          | ~ (v2_funct_1 @ X0)
% 18.69/18.90          | ~ (v1_funct_1 @ X0)
% 18.69/18.90          | ~ (v1_relat_1 @ X0))),
% 18.69/18.90      inference('simplify', [status(thm)], ['23'])).
% 18.69/18.90  thf(t86_xboole_1, axiom,
% 18.69/18.90    (![A:$i,B:$i,C:$i]:
% 18.69/18.90     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 18.69/18.90       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 18.69/18.90  thf('25', plain,
% 18.69/18.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 18.69/18.90         (~ (r1_tarski @ X10 @ X11)
% 18.69/18.90          | ~ (r1_xboole_0 @ X10 @ X12)
% 18.69/18.90          | (r1_tarski @ X10 @ (k4_xboole_0 @ X11 @ X12)))),
% 18.69/18.90      inference('cnf', [status(esa)], [t86_xboole_1])).
% 18.69/18.90  thf('26', plain,
% 18.69/18.90      (![X15 : $i, X16 : $i]:
% 18.69/18.90         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 18.69/18.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.69/18.90  thf('27', plain,
% 18.69/18.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 18.69/18.90         (~ (r1_tarski @ X10 @ X11)
% 18.69/18.90          | ~ (r1_xboole_0 @ X10 @ X12)
% 18.69/18.90          | (r1_tarski @ X10 @ (k6_subset_1 @ X11 @ X12)))),
% 18.69/18.90      inference('demod', [status(thm)], ['25', '26'])).
% 18.69/18.90  thf('28', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 18.69/18.90         (~ (v1_relat_1 @ X1)
% 18.69/18.90          | ~ (v1_funct_1 @ X1)
% 18.69/18.90          | ~ (v2_funct_1 @ X1)
% 18.69/18.90          | (r1_tarski @ (k9_relat_1 @ X1 @ (k6_subset_1 @ X2 @ X0)) @ 
% 18.69/18.90             (k6_subset_1 @ X3 @ (k9_relat_1 @ X1 @ X0)))
% 18.69/18.90          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k6_subset_1 @ X2 @ X0)) @ X3))),
% 18.69/18.90      inference('sup-', [status(thm)], ['24', '27'])).
% 18.69/18.90  thf('29', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (~ (v1_relat_1 @ X1)
% 18.69/18.90          | (r1_tarski @ (k9_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X2)) @ 
% 18.69/18.90             (k6_subset_1 @ (k9_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X2)))
% 18.69/18.90          | ~ (v2_funct_1 @ X1)
% 18.69/18.90          | ~ (v1_funct_1 @ X1)
% 18.69/18.90          | ~ (v1_relat_1 @ X1))),
% 18.69/18.90      inference('sup-', [status(thm)], ['8', '28'])).
% 18.69/18.90  thf('30', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (~ (v1_funct_1 @ X1)
% 18.69/18.90          | ~ (v2_funct_1 @ X1)
% 18.69/18.90          | (r1_tarski @ (k9_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X2)) @ 
% 18.69/18.90             (k6_subset_1 @ (k9_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X2)))
% 18.69/18.90          | ~ (v1_relat_1 @ X1))),
% 18.69/18.90      inference('simplify', [status(thm)], ['29'])).
% 18.69/18.90  thf(t155_relat_1, axiom,
% 18.69/18.90    (![A:$i,B:$i,C:$i]:
% 18.69/18.90     ( ( v1_relat_1 @ C ) =>
% 18.69/18.90       ( r1_tarski @
% 18.69/18.90         ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 18.69/18.90         ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ))).
% 18.69/18.90  thf('31', plain,
% 18.69/18.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 18.69/18.90         ((r1_tarski @ 
% 18.69/18.90           (k6_subset_1 @ (k9_relat_1 @ X18 @ X19) @ (k9_relat_1 @ X18 @ X20)) @ 
% 18.69/18.90           (k9_relat_1 @ X18 @ (k6_subset_1 @ X19 @ X20)))
% 18.69/18.90          | ~ (v1_relat_1 @ X18))),
% 18.69/18.90      inference('cnf', [status(esa)], [t155_relat_1])).
% 18.69/18.90  thf('32', plain,
% 18.69/18.90      (![X3 : $i, X5 : $i]:
% 18.69/18.90         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 18.69/18.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 18.69/18.90  thf('33', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (~ (v1_relat_1 @ X2)
% 18.69/18.90          | ~ (r1_tarski @ (k9_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)) @ 
% 18.69/18.90               (k6_subset_1 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))
% 18.69/18.90          | ((k9_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0))
% 18.69/18.90              = (k6_subset_1 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0))))),
% 18.69/18.90      inference('sup-', [status(thm)], ['31', '32'])).
% 18.69/18.90  thf('34', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (~ (v1_relat_1 @ X1)
% 18.69/18.90          | ~ (v2_funct_1 @ X1)
% 18.69/18.90          | ~ (v1_funct_1 @ X1)
% 18.69/18.90          | ((k9_relat_1 @ X1 @ (k6_subset_1 @ X2 @ X0))
% 18.69/18.90              = (k6_subset_1 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 18.69/18.90          | ~ (v1_relat_1 @ X1))),
% 18.69/18.90      inference('sup-', [status(thm)], ['30', '33'])).
% 18.69/18.90  thf('35', plain,
% 18.69/18.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.69/18.90         (((k9_relat_1 @ X1 @ (k6_subset_1 @ X2 @ X0))
% 18.69/18.90            = (k6_subset_1 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 18.69/18.90          | ~ (v1_funct_1 @ X1)
% 18.69/18.90          | ~ (v2_funct_1 @ X1)
% 18.69/18.90          | ~ (v1_relat_1 @ X1))),
% 18.69/18.90      inference('simplify', [status(thm)], ['34'])).
% 18.69/18.90  thf(t123_funct_1, conjecture,
% 18.69/18.90    (![A:$i,B:$i,C:$i]:
% 18.69/18.90     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 18.69/18.90       ( ( v2_funct_1 @ C ) =>
% 18.69/18.90         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 18.69/18.90           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 18.69/18.90  thf(zf_stmt_0, negated_conjecture,
% 18.69/18.90    (~( ![A:$i,B:$i,C:$i]:
% 18.69/18.90        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 18.69/18.90          ( ( v2_funct_1 @ C ) =>
% 18.69/18.90            ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 18.69/18.90              ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )),
% 18.69/18.90    inference('cnf.neg', [status(esa)], [t123_funct_1])).
% 18.69/18.90  thf('36', plain,
% 18.69/18.90      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B))
% 18.69/18.90         != (k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 18.69/18.90             (k9_relat_1 @ sk_C @ sk_B)))),
% 18.69/18.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.69/18.90  thf('37', plain,
% 18.69/18.90      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B))
% 18.69/18.90          != (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)))
% 18.69/18.90        | ~ (v1_relat_1 @ sk_C)
% 18.69/18.90        | ~ (v2_funct_1 @ sk_C)
% 18.69/18.90        | ~ (v1_funct_1 @ sk_C))),
% 18.69/18.90      inference('sup-', [status(thm)], ['35', '36'])).
% 18.69/18.90  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 18.69/18.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.69/18.90  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 18.69/18.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.69/18.90  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 18.69/18.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.69/18.90  thf('41', plain,
% 18.69/18.90      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B))
% 18.69/18.90         != (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)))),
% 18.69/18.90      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 18.69/18.90  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 18.69/18.90  
% 18.69/18.90  % SZS output end Refutation
% 18.69/18.90  
% 18.74/18.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
