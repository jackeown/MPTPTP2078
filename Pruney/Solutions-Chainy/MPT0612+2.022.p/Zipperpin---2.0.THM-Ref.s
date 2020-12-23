%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j6IMrr2bVB

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:12 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 102 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  471 ( 655 expanded)
%              Number of equality atoms :   33 (  53 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ( ( k6_subset_1 @ X31 @ ( k7_relat_1 @ X31 @ X33 ) )
        = ( k7_relat_1 @ X31 @ ( k6_subset_1 @ X32 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ ( k6_subset_1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X17 @ X18 ) @ X18 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

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

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B_2 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ ( k6_subset_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_A ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_B_2 )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X17 @ X18 ) @ X18 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X12 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X0 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','36'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X30 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X30 @ X28 ) @ X29 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ sk_B_2 ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B_2 ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B_2 ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B_2 ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j6IMrr2bVB
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:34:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 1.13/1.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.13/1.37  % Solved by: fo/fo7.sh
% 1.13/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.37  % done 2322 iterations in 0.901s
% 1.13/1.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.13/1.37  % SZS output start Refutation
% 1.13/1.37  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.13/1.37  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.13/1.37  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.13/1.37  thf(sk_C_type, type, sk_C: $i).
% 1.13/1.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.13/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.13/1.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.13/1.37  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.13/1.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.13/1.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.13/1.37  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.13/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.37  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.13/1.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.13/1.37  thf(t7_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.13/1.37  thf('0', plain,
% 1.13/1.37      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 1.13/1.37      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.13/1.37  thf(t211_relat_1, axiom,
% 1.13/1.37    (![A:$i,B:$i,C:$i]:
% 1.13/1.37     ( ( v1_relat_1 @ C ) =>
% 1.13/1.37       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 1.13/1.37         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 1.13/1.37           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 1.13/1.37  thf('1', plain,
% 1.13/1.37      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.13/1.37         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 1.13/1.37          | ((k6_subset_1 @ X31 @ (k7_relat_1 @ X31 @ X33))
% 1.13/1.37              = (k7_relat_1 @ X31 @ (k6_subset_1 @ X32 @ X33)))
% 1.13/1.37          | ~ (v1_relat_1 @ X31))),
% 1.13/1.37      inference('cnf', [status(esa)], [t211_relat_1])).
% 1.13/1.37  thf('2', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.37         (~ (v1_relat_1 @ X1)
% 1.13/1.37          | ((k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X2))
% 1.13/1.37              = (k7_relat_1 @ X1 @ 
% 1.13/1.37                 (k6_subset_1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2))))),
% 1.13/1.37      inference('sup-', [status(thm)], ['0', '1'])).
% 1.13/1.37  thf(t79_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.13/1.37  thf('3', plain,
% 1.13/1.37      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 1.13/1.37      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.13/1.37  thf(redefinition_k6_subset_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.13/1.37  thf('4', plain,
% 1.13/1.37      (![X24 : $i, X25 : $i]:
% 1.13/1.37         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 1.13/1.37      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.37  thf('5', plain,
% 1.13/1.37      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X17 @ X18) @ X18)),
% 1.13/1.37      inference('demod', [status(thm)], ['3', '4'])).
% 1.13/1.37  thf(t7_xboole_0, axiom,
% 1.13/1.37    (![A:$i]:
% 1.13/1.37     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.13/1.37          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.13/1.37  thf('6', plain,
% 1.13/1.37      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X4) @ X4))),
% 1.13/1.37      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.13/1.37  thf(d1_xboole_0, axiom,
% 1.13/1.37    (![A:$i]:
% 1.13/1.37     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.13/1.37  thf('7', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.13/1.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.37  thf('8', plain,
% 1.13/1.37      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.37      inference('sup-', [status(thm)], ['6', '7'])).
% 1.13/1.37  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.13/1.37  thf('9', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 1.13/1.37      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.13/1.37  thf('10', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['8', '9'])).
% 1.13/1.37  thf(t216_relat_1, conjecture,
% 1.13/1.37    (![A:$i,B:$i,C:$i]:
% 1.13/1.37     ( ( v1_relat_1 @ C ) =>
% 1.13/1.37       ( ( r1_tarski @ A @ B ) =>
% 1.13/1.37         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 1.13/1.37           ( k1_xboole_0 ) ) ) ))).
% 1.13/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.37    (~( ![A:$i,B:$i,C:$i]:
% 1.13/1.37        ( ( v1_relat_1 @ C ) =>
% 1.13/1.37          ( ( r1_tarski @ A @ B ) =>
% 1.13/1.37            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 1.13/1.37              ( k1_xboole_0 ) ) ) ) )),
% 1.13/1.37    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 1.13/1.37  thf('11', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 1.13/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.37  thf(t28_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]:
% 1.13/1.37     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.13/1.37  thf('12', plain,
% 1.13/1.37      (![X10 : $i, X11 : $i]:
% 1.13/1.37         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.13/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.13/1.37  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_A))),
% 1.13/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.13/1.37  thf(t100_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]:
% 1.13/1.37     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.13/1.37  thf('14', plain,
% 1.13/1.37      (![X5 : $i, X6 : $i]:
% 1.13/1.37         ((k4_xboole_0 @ X5 @ X6)
% 1.13/1.37           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.13/1.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.13/1.37  thf('15', plain,
% 1.13/1.37      (![X24 : $i, X25 : $i]:
% 1.13/1.37         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 1.13/1.37      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.37  thf('16', plain,
% 1.13/1.37      (![X5 : $i, X6 : $i]:
% 1.13/1.37         ((k6_subset_1 @ X5 @ X6)
% 1.13/1.37           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.13/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.13/1.37  thf('17', plain,
% 1.13/1.37      (((k6_subset_1 @ sk_A @ sk_B_2) = (k5_xboole_0 @ sk_A @ sk_A))),
% 1.13/1.37      inference('sup+', [status(thm)], ['13', '16'])).
% 1.13/1.37  thf(t84_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i,C:$i]:
% 1.13/1.37     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 1.13/1.37          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 1.13/1.37  thf('18', plain,
% 1.13/1.37      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.37         ((r1_xboole_0 @ X21 @ X22)
% 1.13/1.37          | ~ (r1_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 1.13/1.37          | ~ (r1_xboole_0 @ X21 @ X23))),
% 1.13/1.37      inference('cnf', [status(esa)], [t84_xboole_1])).
% 1.13/1.37  thf('19', plain,
% 1.13/1.37      (![X24 : $i, X25 : $i]:
% 1.13/1.37         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 1.13/1.37      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.37  thf('20', plain,
% 1.13/1.37      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.37         ((r1_xboole_0 @ X21 @ X22)
% 1.13/1.37          | ~ (r1_xboole_0 @ X21 @ (k6_subset_1 @ X22 @ X23))
% 1.13/1.37          | ~ (r1_xboole_0 @ X21 @ X23))),
% 1.13/1.37      inference('demod', [status(thm)], ['18', '19'])).
% 1.13/1.37  thf('21', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_A))
% 1.13/1.37          | ~ (r1_xboole_0 @ X0 @ sk_B_2)
% 1.13/1.37          | (r1_xboole_0 @ X0 @ sk_A))),
% 1.13/1.37      inference('sup-', [status(thm)], ['17', '20'])).
% 1.13/1.37  thf('22', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         (~ (v1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A))
% 1.13/1.37          | (r1_xboole_0 @ X0 @ sk_A)
% 1.13/1.37          | ~ (r1_xboole_0 @ X0 @ sk_B_2))),
% 1.13/1.37      inference('sup-', [status(thm)], ['10', '21'])).
% 1.13/1.37  thf(idempotence_k3_xboole_0, axiom,
% 1.13/1.37    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.13/1.37  thf('23', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.13/1.37      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.13/1.37  thf('24', plain,
% 1.13/1.37      (![X5 : $i, X6 : $i]:
% 1.13/1.37         ((k6_subset_1 @ X5 @ X6)
% 1.13/1.37           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.13/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.13/1.37  thf('25', plain,
% 1.13/1.37      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['23', '24'])).
% 1.13/1.37  thf('26', plain,
% 1.13/1.37      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X17 @ X18) @ X18)),
% 1.13/1.37      inference('demod', [status(thm)], ['3', '4'])).
% 1.13/1.37  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 1.13/1.37      inference('sup+', [status(thm)], ['25', '26'])).
% 1.13/1.37  thf(t69_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]:
% 1.13/1.37     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.13/1.37       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.13/1.37  thf('28', plain,
% 1.13/1.37      (![X15 : $i, X16 : $i]:
% 1.13/1.37         (~ (r1_xboole_0 @ X15 @ X16)
% 1.13/1.37          | ~ (r1_tarski @ X15 @ X16)
% 1.13/1.37          | (v1_xboole_0 @ X15))),
% 1.13/1.37      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.13/1.37  thf('29', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         ((v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 1.13/1.37          | ~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 1.13/1.37      inference('sup-', [status(thm)], ['27', '28'])).
% 1.13/1.37  thf('30', plain,
% 1.13/1.37      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['23', '24'])).
% 1.13/1.37  thf(t36_xboole_1, axiom,
% 1.13/1.37    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.13/1.37  thf('31', plain,
% 1.13/1.37      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.13/1.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.13/1.37  thf('32', plain,
% 1.13/1.37      (![X24 : $i, X25 : $i]:
% 1.13/1.37         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 1.13/1.37      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.37  thf('33', plain,
% 1.13/1.37      (![X12 : $i, X13 : $i]: (r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X12)),
% 1.13/1.37      inference('demod', [status(thm)], ['31', '32'])).
% 1.13/1.37  thf('34', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 1.13/1.37      inference('sup+', [status(thm)], ['30', '33'])).
% 1.13/1.37  thf('35', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 1.13/1.37      inference('demod', [status(thm)], ['29', '34'])).
% 1.13/1.37  thf('36', plain,
% 1.13/1.37      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_A) | ~ (r1_xboole_0 @ X0 @ sk_B_2))),
% 1.13/1.37      inference('demod', [status(thm)], ['22', '35'])).
% 1.13/1.37  thf('37', plain,
% 1.13/1.37      (![X0 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X0 @ sk_B_2) @ sk_A)),
% 1.13/1.37      inference('sup-', [status(thm)], ['5', '36'])).
% 1.13/1.37  thf(t207_relat_1, axiom,
% 1.13/1.37    (![A:$i,B:$i,C:$i]:
% 1.13/1.37     ( ( v1_relat_1 @ C ) =>
% 1.13/1.37       ( ( r1_xboole_0 @ A @ B ) =>
% 1.13/1.37         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 1.13/1.37  thf('38', plain,
% 1.13/1.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.13/1.37         (~ (r1_xboole_0 @ X28 @ X29)
% 1.13/1.37          | ~ (v1_relat_1 @ X30)
% 1.13/1.37          | ((k7_relat_1 @ (k7_relat_1 @ X30 @ X28) @ X29) = (k1_xboole_0)))),
% 1.13/1.37      inference('cnf', [status(esa)], [t207_relat_1])).
% 1.13/1.37  thf('39', plain,
% 1.13/1.37      (![X0 : $i, X1 : $i]:
% 1.13/1.37         (((k7_relat_1 @ (k7_relat_1 @ X1 @ (k6_subset_1 @ X0 @ sk_B_2)) @ sk_A)
% 1.13/1.37            = (k1_xboole_0))
% 1.13/1.37          | ~ (v1_relat_1 @ X1))),
% 1.13/1.37      inference('sup-', [status(thm)], ['37', '38'])).
% 1.13/1.37  thf('40', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         (((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B_2)) @ sk_A)
% 1.13/1.37            = (k1_xboole_0))
% 1.13/1.37          | ~ (v1_relat_1 @ X0)
% 1.13/1.37          | ~ (v1_relat_1 @ X0))),
% 1.13/1.37      inference('sup+', [status(thm)], ['2', '39'])).
% 1.13/1.37  thf('41', plain,
% 1.13/1.37      (![X0 : $i]:
% 1.13/1.37         (~ (v1_relat_1 @ X0)
% 1.13/1.37          | ((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B_2)) @ 
% 1.13/1.37              sk_A) = (k1_xboole_0)))),
% 1.13/1.37      inference('simplify', [status(thm)], ['40'])).
% 1.13/1.37  thf('42', plain,
% 1.13/1.37      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B_2)) @ 
% 1.13/1.37         sk_A) != (k1_xboole_0))),
% 1.13/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.37  thf('43', plain,
% 1.13/1.37      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 1.13/1.37      inference('sup-', [status(thm)], ['41', '42'])).
% 1.13/1.37  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 1.13/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.37  thf('45', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.13/1.37      inference('demod', [status(thm)], ['43', '44'])).
% 1.13/1.37  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 1.13/1.37  
% 1.13/1.37  % SZS output end Refutation
% 1.13/1.37  
% 1.21/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
