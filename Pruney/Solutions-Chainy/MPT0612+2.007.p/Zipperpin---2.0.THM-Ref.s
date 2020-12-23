%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FzkaKvdjcn

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:10 EST 2020

% Result     : Theorem 4.80s
% Output     : Refutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   73 (  92 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  492 ( 673 expanded)
%              Number of equality atoms :   43 (  61 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X26 ) @ X27 )
      | ( ( k7_relat_1 @ X26 @ X27 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( ( k6_subset_1 @ X23 @ ( k7_relat_1 @ X23 @ X25 ) )
        = ( k7_relat_1 @ X23 @ ( k6_subset_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( ( k4_xboole_0 @ X23 @ ( k7_relat_1 @ X23 @ X25 ) )
        = ( k7_relat_1 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) @ X22 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X3 ) @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X3 ) @ X0 ) @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X2 @ ( k7_relat_1 @ X2 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_relat_1 @ X2 ) @ X1 ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ sk_B ) ) @ sk_A )
        = ( k7_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k7_relat_1 @ sk_C @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k7_relat_1 @ sk_C @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FzkaKvdjcn
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 4.80/5.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.80/5.06  % Solved by: fo/fo7.sh
% 4.80/5.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.80/5.06  % done 3994 iterations in 4.563s
% 4.80/5.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.80/5.06  % SZS output start Refutation
% 4.80/5.06  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 4.80/5.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.80/5.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.80/5.06  thf(sk_A_type, type, sk_A: $i).
% 4.80/5.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.80/5.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.80/5.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.80/5.06  thf(sk_C_type, type, sk_C: $i).
% 4.80/5.06  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 4.80/5.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.80/5.06  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.80/5.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.80/5.06  thf(sk_B_type, type, sk_B: $i).
% 4.80/5.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.80/5.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.80/5.06  thf(t3_boole, axiom,
% 4.80/5.06    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.80/5.06  thf('0', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 4.80/5.06      inference('cnf', [status(esa)], [t3_boole])).
% 4.80/5.06  thf(t79_xboole_1, axiom,
% 4.80/5.06    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.80/5.06  thf('1', plain,
% 4.80/5.06      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 4.80/5.06      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.80/5.06  thf('2', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.80/5.06      inference('sup+', [status(thm)], ['0', '1'])).
% 4.80/5.06  thf(t95_relat_1, axiom,
% 4.80/5.06    (![A:$i,B:$i]:
% 4.80/5.06     ( ( v1_relat_1 @ B ) =>
% 4.80/5.06       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 4.80/5.06         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 4.80/5.06  thf('3', plain,
% 4.80/5.06      (![X26 : $i, X27 : $i]:
% 4.80/5.06         (~ (r1_xboole_0 @ (k1_relat_1 @ X26) @ X27)
% 4.80/5.06          | ((k7_relat_1 @ X26 @ X27) = (k1_xboole_0))
% 4.80/5.06          | ~ (v1_relat_1 @ X26))),
% 4.80/5.06      inference('cnf', [status(esa)], [t95_relat_1])).
% 4.80/5.06  thf('4', plain,
% 4.80/5.06      (![X0 : $i]:
% 4.80/5.06         (~ (v1_relat_1 @ X0)
% 4.80/5.06          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.80/5.06      inference('sup-', [status(thm)], ['2', '3'])).
% 4.80/5.06  thf('5', plain,
% 4.80/5.06      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 4.80/5.06      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.80/5.06  thf(d7_xboole_0, axiom,
% 4.80/5.06    (![A:$i,B:$i]:
% 4.80/5.06     ( ( r1_xboole_0 @ A @ B ) <=>
% 4.80/5.06       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 4.80/5.06  thf('6', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]:
% 4.80/5.06         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.80/5.06      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.80/5.06  thf('7', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]:
% 4.80/5.06         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 4.80/5.06      inference('sup-', [status(thm)], ['5', '6'])).
% 4.80/5.06  thf(commutativity_k2_tarski, axiom,
% 4.80/5.06    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.80/5.06  thf('8', plain,
% 4.80/5.06      (![X14 : $i, X15 : $i]:
% 4.80/5.06         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 4.80/5.06      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.80/5.06  thf(t12_setfam_1, axiom,
% 4.80/5.06    (![A:$i,B:$i]:
% 4.80/5.06     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.80/5.06  thf('9', plain,
% 4.80/5.06      (![X18 : $i, X19 : $i]:
% 4.80/5.06         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 4.80/5.06      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.80/5.06  thf('10', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]:
% 4.80/5.06         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 4.80/5.06      inference('sup+', [status(thm)], ['8', '9'])).
% 4.80/5.06  thf('11', plain,
% 4.80/5.06      (![X18 : $i, X19 : $i]:
% 4.80/5.06         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 4.80/5.06      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.80/5.06  thf('12', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.80/5.06      inference('sup+', [status(thm)], ['10', '11'])).
% 4.80/5.06  thf('13', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]:
% 4.80/5.06         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.80/5.06      inference('demod', [status(thm)], ['7', '12'])).
% 4.80/5.06  thf('14', plain,
% 4.80/5.06      (![X0 : $i, X2 : $i]:
% 4.80/5.06         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 4.80/5.06      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.80/5.06  thf('15', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]:
% 4.80/5.06         (((k1_xboole_0) != (k1_xboole_0))
% 4.80/5.06          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.80/5.06      inference('sup-', [status(thm)], ['13', '14'])).
% 4.80/5.06  thf('16', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.80/5.06      inference('simplify', [status(thm)], ['15'])).
% 4.80/5.06  thf(t216_relat_1, conjecture,
% 4.80/5.06    (![A:$i,B:$i,C:$i]:
% 4.80/5.06     ( ( v1_relat_1 @ C ) =>
% 4.80/5.06       ( ( r1_tarski @ A @ B ) =>
% 4.80/5.06         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 4.80/5.06           ( k1_xboole_0 ) ) ) ))).
% 4.80/5.06  thf(zf_stmt_0, negated_conjecture,
% 4.80/5.06    (~( ![A:$i,B:$i,C:$i]:
% 4.80/5.06        ( ( v1_relat_1 @ C ) =>
% 4.80/5.06          ( ( r1_tarski @ A @ B ) =>
% 4.80/5.06            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 4.80/5.06              ( k1_xboole_0 ) ) ) ) )),
% 4.80/5.06    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 4.80/5.06  thf('17', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.80/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/5.06  thf(t63_xboole_1, axiom,
% 4.80/5.06    (![A:$i,B:$i,C:$i]:
% 4.80/5.06     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 4.80/5.06       ( r1_xboole_0 @ A @ C ) ))).
% 4.80/5.06  thf('18', plain,
% 4.80/5.06      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.80/5.06         (~ (r1_tarski @ X7 @ X8)
% 4.80/5.06          | ~ (r1_xboole_0 @ X8 @ X9)
% 4.80/5.06          | (r1_xboole_0 @ X7 @ X9))),
% 4.80/5.06      inference('cnf', [status(esa)], [t63_xboole_1])).
% 4.80/5.06  thf('19', plain,
% 4.80/5.06      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 4.80/5.06      inference('sup-', [status(thm)], ['17', '18'])).
% 4.80/5.06  thf('20', plain,
% 4.80/5.06      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 4.80/5.06      inference('sup-', [status(thm)], ['16', '19'])).
% 4.80/5.06  thf('21', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]:
% 4.80/5.06         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.80/5.06      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.80/5.06  thf('22', plain,
% 4.80/5.06      (![X0 : $i]:
% 4.80/5.06         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 4.80/5.06      inference('sup-', [status(thm)], ['20', '21'])).
% 4.80/5.06  thf('23', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.80/5.06      inference('sup+', [status(thm)], ['10', '11'])).
% 4.80/5.06  thf(t7_xboole_1, axiom,
% 4.80/5.06    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.80/5.06  thf('24', plain,
% 4.80/5.06      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 4.80/5.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.80/5.06  thf(t211_relat_1, axiom,
% 4.80/5.06    (![A:$i,B:$i,C:$i]:
% 4.80/5.06     ( ( v1_relat_1 @ C ) =>
% 4.80/5.06       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 4.80/5.06         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 4.80/5.06           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 4.80/5.06  thf('25', plain,
% 4.80/5.06      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.80/5.06         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 4.80/5.06          | ((k6_subset_1 @ X23 @ (k7_relat_1 @ X23 @ X25))
% 4.80/5.06              = (k7_relat_1 @ X23 @ (k6_subset_1 @ X24 @ X25)))
% 4.80/5.06          | ~ (v1_relat_1 @ X23))),
% 4.80/5.06      inference('cnf', [status(esa)], [t211_relat_1])).
% 4.80/5.06  thf(redefinition_k6_subset_1, axiom,
% 4.80/5.06    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.80/5.06  thf('26', plain,
% 4.80/5.06      (![X16 : $i, X17 : $i]:
% 4.80/5.06         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 4.80/5.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.80/5.06  thf('27', plain,
% 4.80/5.06      (![X16 : $i, X17 : $i]:
% 4.80/5.06         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 4.80/5.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.80/5.06  thf('28', plain,
% 4.80/5.06      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.80/5.06         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 4.80/5.06          | ((k4_xboole_0 @ X23 @ (k7_relat_1 @ X23 @ X25))
% 4.80/5.06              = (k7_relat_1 @ X23 @ (k4_xboole_0 @ X24 @ X25)))
% 4.80/5.06          | ~ (v1_relat_1 @ X23))),
% 4.80/5.06      inference('demod', [status(thm)], ['25', '26', '27'])).
% 4.80/5.06  thf('29', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.80/5.06         (~ (v1_relat_1 @ X1)
% 4.80/5.06          | ((k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X2))
% 4.80/5.06              = (k7_relat_1 @ X1 @ 
% 4.80/5.06                 (k4_xboole_0 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2))))),
% 4.80/5.06      inference('sup-', [status(thm)], ['24', '28'])).
% 4.80/5.06  thf(t100_relat_1, axiom,
% 4.80/5.06    (![A:$i,B:$i,C:$i]:
% 4.80/5.06     ( ( v1_relat_1 @ C ) =>
% 4.80/5.06       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 4.80/5.06         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 4.80/5.06  thf('30', plain,
% 4.80/5.06      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.80/5.06         (((k7_relat_1 @ (k7_relat_1 @ X20 @ X21) @ X22)
% 4.80/5.06            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ X21 @ X22)))
% 4.80/5.06          | ~ (v1_relat_1 @ X20))),
% 4.80/5.06      inference('cnf', [status(esa)], [t100_relat_1])).
% 4.80/5.06  thf('31', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.80/5.06         (((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 4.80/5.06            = (k7_relat_1 @ X1 @ 
% 4.80/5.06               (k3_xboole_0 @ 
% 4.80/5.06                (k4_xboole_0 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X3) @ X0) @ 
% 4.80/5.06                X2)))
% 4.80/5.06          | ~ (v1_relat_1 @ X1)
% 4.80/5.06          | ~ (v1_relat_1 @ X1))),
% 4.80/5.06      inference('sup+', [status(thm)], ['29', '30'])).
% 4.80/5.06  thf('32', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.80/5.06         (~ (v1_relat_1 @ X1)
% 4.80/5.06          | ((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 4.80/5.06              = (k7_relat_1 @ X1 @ 
% 4.80/5.06                 (k3_xboole_0 @ 
% 4.80/5.06                  (k4_xboole_0 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X3) @ X0) @ 
% 4.80/5.06                  X2))))),
% 4.80/5.06      inference('simplify', [status(thm)], ['31'])).
% 4.80/5.06  thf('33', plain,
% 4.80/5.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.80/5.06         (((k7_relat_1 @ (k4_xboole_0 @ X2 @ (k7_relat_1 @ X2 @ X0)) @ X3)
% 4.80/5.06            = (k7_relat_1 @ X2 @ 
% 4.80/5.06               (k3_xboole_0 @ X3 @ 
% 4.80/5.06                (k4_xboole_0 @ (k2_xboole_0 @ (k1_relat_1 @ X2) @ X1) @ X0))))
% 4.80/5.06          | ~ (v1_relat_1 @ X2))),
% 4.80/5.06      inference('sup+', [status(thm)], ['23', '32'])).
% 4.80/5.06  thf('34', plain,
% 4.80/5.06      (![X1 : $i]:
% 4.80/5.06         (((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ sk_B)) @ sk_A)
% 4.80/5.06            = (k7_relat_1 @ X1 @ k1_xboole_0))
% 4.80/5.06          | ~ (v1_relat_1 @ X1))),
% 4.80/5.06      inference('sup+', [status(thm)], ['22', '33'])).
% 4.80/5.06  thf('35', plain,
% 4.80/5.06      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 4.80/5.06         != (k1_xboole_0))),
% 4.80/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/5.06  thf('36', plain,
% 4.80/5.06      (![X16 : $i, X17 : $i]:
% 4.80/5.06         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 4.80/5.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.80/5.06  thf('37', plain,
% 4.80/5.06      (((k7_relat_1 @ (k4_xboole_0 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 4.80/5.06         != (k1_xboole_0))),
% 4.80/5.06      inference('demod', [status(thm)], ['35', '36'])).
% 4.80/5.06  thf('38', plain,
% 4.80/5.06      ((((k7_relat_1 @ sk_C @ k1_xboole_0) != (k1_xboole_0))
% 4.80/5.06        | ~ (v1_relat_1 @ sk_C))),
% 4.80/5.06      inference('sup-', [status(thm)], ['34', '37'])).
% 4.80/5.06  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 4.80/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/5.06  thf('40', plain, (((k7_relat_1 @ sk_C @ k1_xboole_0) != (k1_xboole_0))),
% 4.80/5.06      inference('demod', [status(thm)], ['38', '39'])).
% 4.80/5.06  thf('41', plain,
% 4.80/5.06      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 4.80/5.06      inference('sup-', [status(thm)], ['4', '40'])).
% 4.80/5.06  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 4.80/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.80/5.06  thf('43', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 4.80/5.06      inference('demod', [status(thm)], ['41', '42'])).
% 4.80/5.06  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 4.80/5.06  
% 4.80/5.06  % SZS output end Refutation
% 4.80/5.06  
% 4.80/5.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
