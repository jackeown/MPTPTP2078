%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kE6kIytX4a

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:11 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 108 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  521 ( 768 expanded)
%              Number of equality atoms :   40 (  69 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k6_subset_1 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k6_subset_1 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','28'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ X19 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X11 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k6_subset_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X28 @ ( k7_relat_1 @ X28 @ X29 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( ( k7_relat_1 @ X27 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_subset_1 @ X2 @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_subset_1 @ X2 @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k6_subset_1 @ X22 @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k6_subset_1 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X2 @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','44'])).

thf('46',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kE6kIytX4a
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.27/1.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.27/1.44  % Solved by: fo/fo7.sh
% 1.27/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.44  % done 1829 iterations in 0.984s
% 1.27/1.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.27/1.44  % SZS output start Refutation
% 1.27/1.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.27/1.44  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.27/1.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.27/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.44  thf(sk_C_type, type, sk_C: $i).
% 1.27/1.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.27/1.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.27/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.27/1.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.27/1.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.27/1.44  thf(t216_relat_1, conjecture,
% 1.27/1.44    (![A:$i,B:$i,C:$i]:
% 1.27/1.44     ( ( v1_relat_1 @ C ) =>
% 1.27/1.44       ( ( r1_tarski @ A @ B ) =>
% 1.27/1.44         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 1.27/1.44           ( k1_xboole_0 ) ) ) ))).
% 1.27/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.44    (~( ![A:$i,B:$i,C:$i]:
% 1.27/1.44        ( ( v1_relat_1 @ C ) =>
% 1.27/1.44          ( ( r1_tarski @ A @ B ) =>
% 1.27/1.44            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 1.27/1.44              ( k1_xboole_0 ) ) ) ) )),
% 1.27/1.44    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 1.27/1.44  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf(l32_xboole_1, axiom,
% 1.27/1.44    (![A:$i,B:$i]:
% 1.27/1.44     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.27/1.44  thf('1', plain,
% 1.27/1.44      (![X5 : $i, X7 : $i]:
% 1.27/1.44         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.27/1.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.27/1.44  thf('2', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.27/1.44      inference('sup-', [status(thm)], ['0', '1'])).
% 1.27/1.44  thf(redefinition_k6_subset_1, axiom,
% 1.27/1.44    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.27/1.44  thf('3', plain,
% 1.27/1.44      (![X22 : $i, X23 : $i]:
% 1.27/1.44         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.27/1.44  thf('4', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.27/1.44      inference('demod', [status(thm)], ['2', '3'])).
% 1.27/1.44  thf(t39_xboole_1, axiom,
% 1.27/1.44    (![A:$i,B:$i]:
% 1.27/1.44     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.27/1.44  thf('5', plain,
% 1.27/1.44      (![X8 : $i, X9 : $i]:
% 1.27/1.44         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.27/1.44           = (k2_xboole_0 @ X8 @ X9))),
% 1.27/1.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.27/1.44  thf('6', plain,
% 1.27/1.44      (![X22 : $i, X23 : $i]:
% 1.27/1.44         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.27/1.44  thf('7', plain,
% 1.27/1.44      (![X8 : $i, X9 : $i]:
% 1.27/1.44         ((k2_xboole_0 @ X8 @ (k6_subset_1 @ X9 @ X8))
% 1.27/1.44           = (k2_xboole_0 @ X8 @ X9))),
% 1.27/1.44      inference('demod', [status(thm)], ['5', '6'])).
% 1.27/1.44  thf('8', plain,
% 1.27/1.44      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.27/1.44      inference('sup+', [status(thm)], ['4', '7'])).
% 1.27/1.44  thf(d10_xboole_0, axiom,
% 1.27/1.44    (![A:$i,B:$i]:
% 1.27/1.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.27/1.44  thf('9', plain,
% 1.27/1.44      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.27/1.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.27/1.44  thf('10', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.27/1.44      inference('simplify', [status(thm)], ['9'])).
% 1.27/1.44  thf('11', plain,
% 1.27/1.44      (![X5 : $i, X7 : $i]:
% 1.27/1.44         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.27/1.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.27/1.44  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.27/1.44      inference('sup-', [status(thm)], ['10', '11'])).
% 1.27/1.44  thf('13', plain,
% 1.27/1.44      (![X22 : $i, X23 : $i]:
% 1.27/1.44         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.27/1.44  thf('14', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.27/1.44      inference('demod', [status(thm)], ['12', '13'])).
% 1.27/1.44  thf('15', plain,
% 1.27/1.44      (![X8 : $i, X9 : $i]:
% 1.27/1.44         ((k2_xboole_0 @ X8 @ (k6_subset_1 @ X9 @ X8))
% 1.27/1.44           = (k2_xboole_0 @ X8 @ X9))),
% 1.27/1.44      inference('demod', [status(thm)], ['5', '6'])).
% 1.27/1.44  thf('16', plain,
% 1.27/1.44      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 1.27/1.44      inference('sup+', [status(thm)], ['14', '15'])).
% 1.27/1.44  thf(t7_xboole_1, axiom,
% 1.27/1.44    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.27/1.44  thf('17', plain,
% 1.27/1.44      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.27/1.44      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.27/1.44  thf('18', plain,
% 1.27/1.44      (![X2 : $i, X4 : $i]:
% 1.27/1.44         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.27/1.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.27/1.44  thf('19', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i]:
% 1.27/1.44         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.27/1.44          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.27/1.44      inference('sup-', [status(thm)], ['17', '18'])).
% 1.27/1.44  thf('20', plain,
% 1.27/1.44      (![X0 : $i]:
% 1.27/1.44         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0)
% 1.27/1.44          | ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 1.27/1.44      inference('sup-', [status(thm)], ['16', '19'])).
% 1.27/1.44  thf('21', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.27/1.44      inference('simplify', [status(thm)], ['9'])).
% 1.27/1.44  thf('22', plain,
% 1.27/1.44      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 1.27/1.44      inference('sup+', [status(thm)], ['14', '15'])).
% 1.27/1.44  thf(t73_xboole_1, axiom,
% 1.27/1.44    (![A:$i,B:$i,C:$i]:
% 1.27/1.44     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.27/1.44       ( r1_tarski @ A @ B ) ))).
% 1.27/1.44  thf('23', plain,
% 1.27/1.44      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.44         ((r1_tarski @ X15 @ X16)
% 1.27/1.44          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.27/1.44          | ~ (r1_xboole_0 @ X15 @ X17))),
% 1.27/1.44      inference('cnf', [status(esa)], [t73_xboole_1])).
% 1.27/1.44  thf('24', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i]:
% 1.27/1.44         (~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 1.27/1.44          | ~ (r1_xboole_0 @ X1 @ k1_xboole_0)
% 1.27/1.44          | (r1_tarski @ X1 @ X0))),
% 1.27/1.44      inference('sup-', [status(thm)], ['22', '23'])).
% 1.27/1.44  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.27/1.44  thf('25', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 1.27/1.44      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.27/1.44  thf('26', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i]:
% 1.27/1.44         (~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X0)) | (r1_tarski @ X1 @ X0))),
% 1.27/1.44      inference('demod', [status(thm)], ['24', '25'])).
% 1.27/1.44  thf('27', plain, (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0)),
% 1.27/1.44      inference('sup-', [status(thm)], ['21', '26'])).
% 1.27/1.44  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.27/1.44      inference('demod', [status(thm)], ['20', '27'])).
% 1.27/1.44  thf('29', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.27/1.44      inference('demod', [status(thm)], ['8', '28'])).
% 1.27/1.44  thf(t79_xboole_1, axiom,
% 1.27/1.44    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.27/1.44  thf('30', plain,
% 1.27/1.44      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 1.27/1.44      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.27/1.44  thf('31', plain,
% 1.27/1.44      (![X22 : $i, X23 : $i]:
% 1.27/1.44         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.27/1.44  thf('32', plain,
% 1.27/1.44      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ X19)),
% 1.27/1.44      inference('demod', [status(thm)], ['30', '31'])).
% 1.27/1.44  thf(t70_xboole_1, axiom,
% 1.27/1.44    (![A:$i,B:$i,C:$i]:
% 1.27/1.44     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.27/1.44            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.27/1.44       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.27/1.44            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.27/1.44  thf('33', plain,
% 1.27/1.44      (![X11 : $i, X12 : $i, X14 : $i]:
% 1.27/1.44         ((r1_xboole_0 @ X11 @ X14)
% 1.27/1.44          | ~ (r1_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X14)))),
% 1.27/1.44      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.27/1.44  thf('34', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.44         (r1_xboole_0 @ (k6_subset_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 1.27/1.44      inference('sup-', [status(thm)], ['32', '33'])).
% 1.27/1.44  thf(symmetry_r1_xboole_0, axiom,
% 1.27/1.44    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.27/1.44  thf('35', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i]:
% 1.27/1.44         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.27/1.44      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.27/1.44  thf('36', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.44         (r1_xboole_0 @ X0 @ (k6_subset_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.27/1.44      inference('sup-', [status(thm)], ['34', '35'])).
% 1.27/1.44  thf(t212_relat_1, axiom,
% 1.27/1.44    (![A:$i,B:$i]:
% 1.27/1.44     ( ( v1_relat_1 @ B ) =>
% 1.27/1.44       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 1.27/1.44         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.27/1.44  thf('37', plain,
% 1.27/1.44      (![X28 : $i, X29 : $i]:
% 1.27/1.44         (((k1_relat_1 @ (k6_subset_1 @ X28 @ (k7_relat_1 @ X28 @ X29)))
% 1.27/1.44            = (k6_subset_1 @ (k1_relat_1 @ X28) @ X29))
% 1.27/1.44          | ~ (v1_relat_1 @ X28))),
% 1.27/1.44      inference('cnf', [status(esa)], [t212_relat_1])).
% 1.27/1.44  thf(t187_relat_1, axiom,
% 1.27/1.44    (![A:$i]:
% 1.27/1.44     ( ( v1_relat_1 @ A ) =>
% 1.27/1.44       ( ![B:$i]:
% 1.27/1.44         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 1.27/1.44           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.27/1.44  thf('38', plain,
% 1.27/1.44      (![X26 : $i, X27 : $i]:
% 1.27/1.44         (~ (r1_xboole_0 @ X26 @ (k1_relat_1 @ X27))
% 1.27/1.44          | ((k7_relat_1 @ X27 @ X26) = (k1_xboole_0))
% 1.27/1.44          | ~ (v1_relat_1 @ X27))),
% 1.27/1.44      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.27/1.44  thf('39', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.44         (~ (r1_xboole_0 @ X2 @ (k6_subset_1 @ (k1_relat_1 @ X1) @ X0))
% 1.27/1.44          | ~ (v1_relat_1 @ X1)
% 1.27/1.44          | ~ (v1_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 1.27/1.44          | ((k7_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 1.27/1.44              = (k1_xboole_0)))),
% 1.27/1.44      inference('sup-', [status(thm)], ['37', '38'])).
% 1.27/1.44  thf('40', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.44         (((k7_relat_1 @ 
% 1.27/1.44            (k6_subset_1 @ X2 @ (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 1.27/1.44            X0) = (k1_xboole_0))
% 1.27/1.44          | ~ (v1_relat_1 @ 
% 1.27/1.44               (k6_subset_1 @ X2 @ (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 1.27/1.44          | ~ (v1_relat_1 @ X2))),
% 1.27/1.44      inference('sup-', [status(thm)], ['36', '39'])).
% 1.27/1.44  thf(fc2_relat_1, axiom,
% 1.27/1.44    (![A:$i,B:$i]:
% 1.27/1.44     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 1.27/1.44  thf('41', plain,
% 1.27/1.44      (![X24 : $i, X25 : $i]:
% 1.27/1.44         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k4_xboole_0 @ X24 @ X25)))),
% 1.27/1.44      inference('cnf', [status(esa)], [fc2_relat_1])).
% 1.27/1.44  thf('42', plain,
% 1.27/1.44      (![X22 : $i, X23 : $i]:
% 1.27/1.44         ((k6_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.27/1.44  thf('43', plain,
% 1.27/1.44      (![X24 : $i, X25 : $i]:
% 1.27/1.44         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k6_subset_1 @ X24 @ X25)))),
% 1.27/1.44      inference('demod', [status(thm)], ['41', '42'])).
% 1.27/1.44  thf('44', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.44         (~ (v1_relat_1 @ X2)
% 1.27/1.44          | ((k7_relat_1 @ 
% 1.27/1.44              (k6_subset_1 @ X2 @ (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 1.27/1.44              X0) = (k1_xboole_0)))),
% 1.27/1.44      inference('clc', [status(thm)], ['40', '43'])).
% 1.27/1.44  thf('45', plain,
% 1.27/1.44      (![X0 : $i]:
% 1.27/1.44         (((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 1.27/1.44            = (k1_xboole_0))
% 1.27/1.44          | ~ (v1_relat_1 @ X0))),
% 1.27/1.44      inference('sup+', [status(thm)], ['29', '44'])).
% 1.27/1.44  thf('46', plain,
% 1.27/1.44      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 1.27/1.44         != (k1_xboole_0))),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('47', plain,
% 1.27/1.44      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 1.27/1.44      inference('sup-', [status(thm)], ['45', '46'])).
% 1.27/1.44  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('49', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.27/1.44      inference('demod', [status(thm)], ['47', '48'])).
% 1.27/1.44  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 1.27/1.44  
% 1.27/1.44  % SZS output end Refutation
% 1.27/1.44  
% 1.27/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
