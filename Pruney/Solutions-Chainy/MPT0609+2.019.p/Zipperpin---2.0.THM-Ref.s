%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DOoAVS2q2n

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:01 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   77 (  93 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  506 ( 668 expanded)
%              Number of equality atoms :   45 (  61 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X36 @ ( k7_relat_1 @ X36 @ X37 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X40 ) @ X41 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t213_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
        = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
          = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t213_relat_1])).

thf('2',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X25 @ X26 ) @ ( sk_D_2 @ X25 @ X26 ) ) @ X26 )
      | ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X22: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k6_subset_1 @ X9 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['17','23'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k6_subset_1 @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X22: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ X14 @ X15 ) @ ( k6_subset_1 @ X14 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','41'])).

thf('43',plain,
    ( ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DOoAVS2q2n
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.72  % Solved by: fo/fo7.sh
% 0.47/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.72  % done 506 iterations in 0.266s
% 0.47/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.72  % SZS output start Refutation
% 0.47/0.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.72  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.47/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.72  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.47/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.72  thf(t212_relat_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ B ) =>
% 0.47/0.72       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.47/0.72         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.72  thf('0', plain,
% 0.47/0.72      (![X36 : $i, X37 : $i]:
% 0.47/0.72         (((k1_relat_1 @ (k6_subset_1 @ X36 @ (k7_relat_1 @ X36 @ X37)))
% 0.47/0.72            = (k6_subset_1 @ (k1_relat_1 @ X36) @ X37))
% 0.47/0.72          | ~ (v1_relat_1 @ X36))),
% 0.47/0.72      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.47/0.72  thf(t90_relat_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ B ) =>
% 0.47/0.72       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.47/0.72         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.72  thf('1', plain,
% 0.47/0.72      (![X40 : $i, X41 : $i]:
% 0.47/0.72         (((k1_relat_1 @ (k7_relat_1 @ X40 @ X41))
% 0.47/0.72            = (k3_xboole_0 @ (k1_relat_1 @ X40) @ X41))
% 0.47/0.72          | ~ (v1_relat_1 @ X40))),
% 0.47/0.72      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.47/0.72  thf(t213_relat_1, conjecture,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ B ) =>
% 0.47/0.72       ( ( k6_subset_1 @
% 0.47/0.72           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.47/0.72         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.47/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.72    (~( ![A:$i,B:$i]:
% 0.47/0.72        ( ( v1_relat_1 @ B ) =>
% 0.47/0.72          ( ( k6_subset_1 @
% 0.47/0.72              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.47/0.72            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.47/0.72    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.47/0.72  thf('2', plain,
% 0.47/0.72      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.47/0.72         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.47/0.72         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('3', plain,
% 0.47/0.72      ((((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.47/0.72          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.47/0.72          != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.47/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.72  thf('4', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.72  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('6', plain,
% 0.47/0.72      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.47/0.72         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.47/0.72         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.47/0.72      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.47/0.72  thf(d3_relat_1, axiom,
% 0.47/0.72    (![A:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ A ) =>
% 0.47/0.72       ( ![B:$i]:
% 0.47/0.72         ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.72           ( ![C:$i,D:$i]:
% 0.47/0.72             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.47/0.72               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.47/0.72  thf('7', plain,
% 0.47/0.72      (![X25 : $i, X26 : $i]:
% 0.47/0.72         ((r2_hidden @ 
% 0.47/0.72           (k4_tarski @ (sk_C @ X25 @ X26) @ (sk_D_2 @ X25 @ X26)) @ X26)
% 0.47/0.72          | (r1_tarski @ X26 @ X25)
% 0.47/0.72          | ~ (v1_relat_1 @ X26))),
% 0.47/0.72      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.47/0.72  thf(t4_boole, axiom,
% 0.47/0.72    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.72  thf('8', plain,
% 0.47/0.72      (![X22 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.47/0.72      inference('cnf', [status(esa)], [t4_boole])).
% 0.47/0.72  thf(redefinition_k6_subset_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.47/0.72  thf('9', plain,
% 0.47/0.72      (![X23 : $i, X24 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.72  thf('10', plain,
% 0.47/0.72      (![X22 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.47/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.72  thf(d5_xboole_0, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.47/0.72       ( ![D:$i]:
% 0.47/0.72         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.72           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.47/0.72  thf('11', plain,
% 0.47/0.72      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.72         (~ (r2_hidden @ X12 @ X11)
% 0.47/0.72          | ~ (r2_hidden @ X12 @ X10)
% 0.47/0.72          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.47/0.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.72  thf('12', plain,
% 0.47/0.72      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.47/0.72         (~ (r2_hidden @ X12 @ X10)
% 0.47/0.72          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.47/0.72      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.72  thf('13', plain,
% 0.47/0.72      (![X23 : $i, X24 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.72  thf('14', plain,
% 0.47/0.72      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.47/0.72         (~ (r2_hidden @ X12 @ X10)
% 0.47/0.72          | ~ (r2_hidden @ X12 @ (k6_subset_1 @ X9 @ X10)))),
% 0.47/0.72      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.72  thf('15', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.47/0.72      inference('sup-', [status(thm)], ['10', '14'])).
% 0.47/0.72  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.47/0.72      inference('condensation', [status(thm)], ['15'])).
% 0.47/0.72  thf('17', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v1_relat_1 @ k1_xboole_0) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.47/0.72      inference('sup-', [status(thm)], ['7', '16'])).
% 0.47/0.72  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf(t110_relat_1, axiom,
% 0.47/0.72    (![A:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ A ) =>
% 0.47/0.72       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.72  thf('19', plain,
% 0.47/0.72      (![X32 : $i]:
% 0.47/0.72         (((k7_relat_1 @ X32 @ k1_xboole_0) = (k1_xboole_0))
% 0.47/0.72          | ~ (v1_relat_1 @ X32))),
% 0.47/0.72      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.47/0.72  thf(dt_k7_relat_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.47/0.72  thf('20', plain,
% 0.47/0.72      (![X30 : $i, X31 : $i]:
% 0.47/0.72         (~ (v1_relat_1 @ X30) | (v1_relat_1 @ (k7_relat_1 @ X30 @ X31)))),
% 0.47/0.72      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.47/0.72  thf('21', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         ((v1_relat_1 @ k1_xboole_0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['19', '20'])).
% 0.47/0.72  thf('22', plain,
% 0.47/0.72      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.72      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.72  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.72      inference('sup-', [status(thm)], ['18', '22'])).
% 0.47/0.72  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.72      inference('demod', [status(thm)], ['17', '23'])).
% 0.47/0.72  thf(t12_xboole_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.72  thf('25', plain,
% 0.47/0.72      (![X17 : $i, X18 : $i]:
% 0.47/0.72         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.47/0.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.72  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.72  thf(t40_xboole_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]:
% 0.47/0.72     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.47/0.72  thf('27', plain,
% 0.47/0.72      (![X20 : $i, X21 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.47/0.72           = (k4_xboole_0 @ X20 @ X21))),
% 0.47/0.72      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.47/0.72  thf('28', plain,
% 0.47/0.72      (![X23 : $i, X24 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.72  thf('29', plain,
% 0.47/0.72      (![X23 : $i, X24 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.72  thf('30', plain,
% 0.47/0.72      (![X20 : $i, X21 : $i]:
% 0.47/0.72         ((k6_subset_1 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.47/0.72           = (k6_subset_1 @ X20 @ X21))),
% 0.47/0.72      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.47/0.72  thf('31', plain,
% 0.47/0.72      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ k1_xboole_0 @ X0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['26', '30'])).
% 0.47/0.72  thf('32', plain,
% 0.47/0.72      (![X22 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.47/0.72      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.72  thf('33', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.72      inference('demod', [status(thm)], ['31', '32'])).
% 0.47/0.72  thf(l36_xboole_1, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.47/0.72       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.47/0.72  thf('34', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.72         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 0.47/0.72           = (k2_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ 
% 0.47/0.72              (k4_xboole_0 @ X14 @ X16)))),
% 0.47/0.72      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.47/0.72  thf('35', plain,
% 0.47/0.72      (![X23 : $i, X24 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.72  thf('36', plain,
% 0.47/0.72      (![X23 : $i, X24 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.72  thf('37', plain,
% 0.47/0.72      (![X23 : $i, X24 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.72  thf('38', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 0.47/0.72           = (k2_xboole_0 @ (k6_subset_1 @ X14 @ X15) @ 
% 0.47/0.72              (k6_subset_1 @ X14 @ X16)))),
% 0.47/0.72      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.47/0.72  thf('39', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.72           = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ k1_xboole_0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['33', '38'])).
% 0.47/0.72  thf(t1_boole, axiom,
% 0.47/0.72    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.72  thf('40', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.47/0.72      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.72  thf('41', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         ((k6_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.47/0.72           = (k6_subset_1 @ X0 @ X1))),
% 0.47/0.72      inference('demod', [status(thm)], ['39', '40'])).
% 0.47/0.72  thf('42', plain,
% 0.47/0.72      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.47/0.72         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.47/0.72      inference('demod', [status(thm)], ['6', '41'])).
% 0.47/0.72  thf('43', plain,
% 0.47/0.72      ((((k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.47/0.72          != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.47/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.72      inference('sup-', [status(thm)], ['0', '42'])).
% 0.47/0.72  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('45', plain,
% 0.47/0.72      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.47/0.72         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['43', '44'])).
% 0.47/0.72  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.47/0.72  
% 0.47/0.72  % SZS output end Refutation
% 0.47/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
