%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yYQjTk4mK8

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:09 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   70 (  80 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  505 ( 613 expanded)
%              Number of equality atoms :   36 (  45 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ( ( k6_subset_1 @ X26 @ ( k7_relat_1 @ X26 @ X28 ) )
        = ( k7_relat_1 @ X26 @ ( k6_subset_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ( ( k4_xboole_0 @ X26 @ ( k7_relat_1 @ X26 @ X28 ) )
        = ( k7_relat_1 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

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

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 )
      | ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t191_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ ( k6_subset_1 @ ( k1_relat_1 @ X24 ) @ X25 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t191_relat_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ ( k4_xboole_0 @ ( k1_relat_1 @ X24 ) @ X25 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k7_relat_1 @ X23 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('36',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yYQjTk4mK8
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 217 iterations in 0.197s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.45/0.65      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.65  thf(t211_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ C ) =>
% 0.45/0.65       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.45/0.65         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.45/0.65           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.45/0.65          | ((k6_subset_1 @ X26 @ (k7_relat_1 @ X26 @ X28))
% 0.45/0.65              = (k7_relat_1 @ X26 @ (k6_subset_1 @ X27 @ X28)))
% 0.45/0.65          | ~ (v1_relat_1 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.45/0.65  thf(redefinition_k6_subset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.45/0.65          | ((k4_xboole_0 @ X26 @ (k7_relat_1 @ X26 @ X28))
% 0.45/0.65              = (k7_relat_1 @ X26 @ (k4_xboole_0 @ X27 @ X28)))
% 0.45/0.65          | ~ (v1_relat_1 @ X26))),
% 0.45/0.65      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.65              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '5'])).
% 0.45/0.65  thf(t79_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.45/0.65      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.65  thf(t4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X0 @ X1)
% 0.45/0.65          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf(commutativity_k2_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.65  thf(t12_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.45/0.65          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['8', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '16'])).
% 0.45/0.65  thf(t216_relat_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ C ) =>
% 0.45/0.65       ( ( r1_tarski @ A @ B ) =>
% 0.45/0.65         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.45/0.65           ( k1_xboole_0 ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.65        ( ( v1_relat_1 @ C ) =>
% 0.45/0.65          ( ( r1_tarski @ A @ B ) =>
% 0.45/0.65            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.45/0.65              ( k1_xboole_0 ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.45/0.65  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t63_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.45/0.65       ( r1_xboole_0 @ A @ C ) ))).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X9 @ X10)
% 0.45/0.65          | ~ (r1_xboole_0 @ X10 @ X11)
% 0.45/0.65          | (r1_xboole_0 @ X9 @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '20'])).
% 0.45/0.65  thf(dt_k7_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.65  thf(t191_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ B ) =>
% 0.45/0.65       ( ( k1_relat_1 @
% 0.45/0.65           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.45/0.65         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         (((k1_relat_1 @ 
% 0.45/0.65            (k7_relat_1 @ X24 @ (k6_subset_1 @ (k1_relat_1 @ X24) @ X25)))
% 0.45/0.65            = (k6_subset_1 @ (k1_relat_1 @ X24) @ X25))
% 0.45/0.65          | ~ (v1_relat_1 @ X24))),
% 0.45/0.65      inference('cnf', [status(esa)], [t191_relat_1])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         (((k1_relat_1 @ 
% 0.45/0.65            (k7_relat_1 @ X24 @ (k4_xboole_0 @ (k1_relat_1 @ X24) @ X25)))
% 0.45/0.65            = (k4_xboole_0 @ (k1_relat_1 @ X24) @ X25))
% 0.45/0.65          | ~ (v1_relat_1 @ X24))),
% 0.45/0.65      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.45/0.65  thf(t187_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.45/0.65           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X22 : $i, X23 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ X22 @ (k1_relat_1 @ X23))
% 0.45/0.65          | ((k7_relat_1 @ X23 @ X22) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X23))),
% 0.45/0.65      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ X2 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ 
% 0.45/0.65               (k7_relat_1 @ X1 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.45/0.65          | ((k7_relat_1 @ 
% 0.45/0.65              (k7_relat_1 @ X1 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)) @ X2)
% 0.45/0.65              = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X1)
% 0.45/0.65          | ((k7_relat_1 @ 
% 0.45/0.65              (k7_relat_1 @ X1 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)) @ X2)
% 0.45/0.65              = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (r1_xboole_0 @ X2 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['22', '28'])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ X2 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.45/0.65          | ((k7_relat_1 @ 
% 0.45/0.65              (k7_relat_1 @ X1 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)) @ X2)
% 0.45/0.65              = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X1))),
% 0.45/0.65      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k7_relat_1 @ 
% 0.45/0.65              (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ sk_B)) @ 
% 0.45/0.65              sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['21', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.45/0.65            = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['6', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.45/0.65              = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (((k7_relat_1 @ (k6_subset_1 @ sk_C_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.45/0.65         sk_A) != (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (((k7_relat_1 @ (k4_xboole_0 @ sk_C_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.45/0.65         sk_A) != (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['33', '36'])).
% 0.45/0.65  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('39', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
