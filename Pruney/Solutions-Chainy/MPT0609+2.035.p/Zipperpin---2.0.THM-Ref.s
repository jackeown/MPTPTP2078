%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OLq8On8pWS

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:03 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   63 (  95 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  664 ( 980 expanded)
%              Number of equality atoms :   52 (  84 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X13 @ X14 )
        = ( k7_relat_1 @ X13 @ ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X15 @ ( k7_relat_1 @ X15 @ X16 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X15 @ ( k7_relat_1 @ X15 @ X16 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X13 @ X14 )
        = ( k7_relat_1 @ X13 @ ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t109_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X10 @ ( k6_subset_1 @ X11 @ X12 ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ X10 @ X11 ) @ ( k7_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t109_relat_1])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
        = ( k4_xboole_0 @ ( k7_relat_1 @ X10 @ X11 ) @ ( k7_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
        = ( k4_xboole_0 @ ( k7_relat_1 @ X10 @ X11 ) @ ( k7_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
        = ( k4_xboole_0 @ ( k7_relat_1 @ X10 @ X11 ) @ ( k7_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X15 @ ( k7_relat_1 @ X15 @ X16 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

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

thf('36',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OLq8On8pWS
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.84  % Solved by: fo/fo7.sh
% 0.60/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.84  % done 315 iterations in 0.392s
% 0.60/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.84  % SZS output start Refutation
% 0.60/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.84  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.60/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.84  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.60/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.84  thf(t192_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( ( k7_relat_1 @ B @ A ) =
% 0.60/0.84         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.60/0.84  thf('0', plain,
% 0.60/0.84      (![X13 : $i, X14 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X13 @ X14)
% 0.60/0.84            = (k7_relat_1 @ X13 @ (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14)))
% 0.60/0.84          | ~ (v1_relat_1 @ X13))),
% 0.60/0.84      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.60/0.84  thf(t212_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.60/0.84         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.84  thf('1', plain,
% 0.60/0.84      (![X15 : $i, X16 : $i]:
% 0.60/0.84         (((k1_relat_1 @ (k6_subset_1 @ X15 @ (k7_relat_1 @ X15 @ X16)))
% 0.60/0.84            = (k6_subset_1 @ (k1_relat_1 @ X15) @ X16))
% 0.60/0.84          | ~ (v1_relat_1 @ X15))),
% 0.60/0.84      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.60/0.84  thf(redefinition_k6_subset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.60/0.84  thf('2', plain,
% 0.60/0.84      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.84  thf('3', plain,
% 0.60/0.84      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.84  thf('4', plain,
% 0.60/0.84      (![X15 : $i, X16 : $i]:
% 0.60/0.84         (((k1_relat_1 @ (k4_xboole_0 @ X15 @ (k7_relat_1 @ X15 @ X16)))
% 0.60/0.84            = (k4_xboole_0 @ (k1_relat_1 @ X15) @ X16))
% 0.60/0.84          | ~ (v1_relat_1 @ X15))),
% 0.60/0.84      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.60/0.84  thf('5', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.60/0.84            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.60/0.84               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.60/0.84          | ~ (v1_relat_1 @ X1)
% 0.60/0.84          | ~ (v1_relat_1 @ X1))),
% 0.60/0.84      inference('sup+', [status(thm)], ['0', '4'])).
% 0.60/0.84  thf('6', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X1)
% 0.60/0.84          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.60/0.84              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.60/0.84                 (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 0.60/0.84      inference('simplify', [status(thm)], ['5'])).
% 0.60/0.84  thf('7', plain,
% 0.60/0.84      (![X13 : $i, X14 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X13 @ X14)
% 0.60/0.84            = (k7_relat_1 @ X13 @ (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14)))
% 0.60/0.84          | ~ (v1_relat_1 @ X13))),
% 0.60/0.84      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.60/0.84  thf(t98_relat_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ A ) =>
% 0.60/0.84       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.60/0.84  thf('8', plain,
% 0.60/0.84      (![X17 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (X17))
% 0.60/0.84          | ~ (v1_relat_1 @ X17))),
% 0.60/0.84      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.60/0.84  thf(t109_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ C ) =>
% 0.60/0.84       ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.60/0.84         ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.60/0.84  thf('9', plain,
% 0.60/0.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X10 @ (k6_subset_1 @ X11 @ X12))
% 0.60/0.84            = (k6_subset_1 @ (k7_relat_1 @ X10 @ X11) @ 
% 0.60/0.84               (k7_relat_1 @ X10 @ X12)))
% 0.60/0.84          | ~ (v1_relat_1 @ X10))),
% 0.60/0.84      inference('cnf', [status(esa)], [t109_relat_1])).
% 0.60/0.84  thf('10', plain,
% 0.60/0.84      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.84  thf('11', plain,
% 0.60/0.84      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.84  thf('12', plain,
% 0.60/0.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.60/0.84            = (k4_xboole_0 @ (k7_relat_1 @ X10 @ X11) @ 
% 0.60/0.84               (k7_relat_1 @ X10 @ X12)))
% 0.60/0.84          | ~ (v1_relat_1 @ X10))),
% 0.60/0.84      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.60/0.84  thf('13', plain,
% 0.60/0.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.60/0.84            = (k4_xboole_0 @ (k7_relat_1 @ X10 @ X11) @ 
% 0.60/0.84               (k7_relat_1 @ X10 @ X12)))
% 0.60/0.84          | ~ (v1_relat_1 @ X10))),
% 0.60/0.84      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.60/0.84  thf(t48_xboole_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.60/0.84  thf('14', plain,
% 0.60/0.84      (![X2 : $i, X3 : $i]:
% 0.60/0.84         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.60/0.84           = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.84  thf('15', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         (((k4_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ 
% 0.60/0.84            (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.60/0.84            = (k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ (k7_relat_1 @ X2 @ X0)))
% 0.60/0.84          | ~ (v1_relat_1 @ X2))),
% 0.60/0.84      inference('sup+', [status(thm)], ['13', '14'])).
% 0.60/0.84  thf('16', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.60/0.84            = (k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ (k7_relat_1 @ X2 @ X0)))
% 0.60/0.84          | ~ (v1_relat_1 @ X2)
% 0.60/0.84          | ~ (v1_relat_1 @ X2))),
% 0.60/0.84      inference('sup+', [status(thm)], ['12', '15'])).
% 0.60/0.84  thf('17', plain,
% 0.60/0.84      (![X2 : $i, X3 : $i]:
% 0.60/0.84         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.60/0.84           = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.84  thf('18', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.60/0.84            = (k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ (k7_relat_1 @ X2 @ X0)))
% 0.60/0.84          | ~ (v1_relat_1 @ X2)
% 0.60/0.84          | ~ (v1_relat_1 @ X2))),
% 0.60/0.84      inference('demod', [status(thm)], ['16', '17'])).
% 0.60/0.84  thf('19', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X2)
% 0.60/0.84          | ((k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.60/0.84              = (k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ (k7_relat_1 @ X2 @ X0))))),
% 0.60/0.84      inference('simplify', [status(thm)], ['18'])).
% 0.60/0.84  thf('20', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.60/0.84            = (k3_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1)))
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | ~ (v1_relat_1 @ X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['8', '19'])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X0)
% 0.60/0.84          | ((k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.60/0.84              = (k3_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))))),
% 0.60/0.84      inference('simplify', [status(thm)], ['20'])).
% 0.60/0.84  thf('22', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X1 @ X0) = (k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.60/0.84          | ~ (v1_relat_1 @ X1)
% 0.60/0.84          | ~ (v1_relat_1 @ X1))),
% 0.60/0.84      inference('sup+', [status(thm)], ['7', '21'])).
% 0.60/0.84  thf('23', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X1)
% 0.60/0.84          | ((k7_relat_1 @ X1 @ X0)
% 0.60/0.84              = (k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.60/0.84      inference('simplify', [status(thm)], ['22'])).
% 0.60/0.84  thf('24', plain,
% 0.60/0.84      (![X17 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (X17))
% 0.60/0.84          | ~ (v1_relat_1 @ X17))),
% 0.60/0.84      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.60/0.84  thf('25', plain,
% 0.60/0.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.60/0.84            = (k4_xboole_0 @ (k7_relat_1 @ X10 @ X11) @ 
% 0.60/0.84               (k7_relat_1 @ X10 @ X12)))
% 0.60/0.84          | ~ (v1_relat_1 @ X10))),
% 0.60/0.84      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.60/0.84            = (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1)))
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | ~ (v1_relat_1 @ X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['24', '25'])).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X0)
% 0.60/0.84          | ((k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.60/0.84              = (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))))),
% 0.60/0.84      inference('simplify', [status(thm)], ['26'])).
% 0.60/0.84  thf('28', plain,
% 0.60/0.84      (![X15 : $i, X16 : $i]:
% 0.60/0.84         (((k1_relat_1 @ (k4_xboole_0 @ X15 @ (k7_relat_1 @ X15 @ X16)))
% 0.60/0.84            = (k4_xboole_0 @ (k1_relat_1 @ X15) @ X16))
% 0.60/0.84          | ~ (v1_relat_1 @ X15))),
% 0.60/0.84      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.60/0.84  thf('29', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k1_relat_1 @ 
% 0.60/0.84            (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))))
% 0.60/0.84            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.60/0.84               (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.60/0.84          | ~ (v1_relat_1 @ X1)
% 0.60/0.84          | ~ (v1_relat_1 @ X1))),
% 0.60/0.84      inference('sup+', [status(thm)], ['27', '28'])).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      (![X2 : $i, X3 : $i]:
% 0.60/0.84         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.60/0.84           = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.84  thf('31', plain,
% 0.60/0.84      (![X2 : $i, X3 : $i]:
% 0.60/0.84         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.60/0.84           = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k1_relat_1 @ (k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.60/0.84            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.60/0.84          | ~ (v1_relat_1 @ X1)
% 0.60/0.84          | ~ (v1_relat_1 @ X1))),
% 0.60/0.84      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X1)
% 0.60/0.84          | ((k1_relat_1 @ (k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.60/0.84              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['32'])).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.60/0.84            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.60/0.84          | ~ (v1_relat_1 @ X1)
% 0.60/0.84          | ~ (v1_relat_1 @ X1))),
% 0.60/0.84      inference('sup+', [status(thm)], ['23', '33'])).
% 0.60/0.84  thf('35', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X1)
% 0.60/0.84          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.60/0.84              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['34'])).
% 0.60/0.84  thf(t213_relat_1, conjecture,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( ( k6_subset_1 @
% 0.60/0.84           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.60/0.84         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.84    (~( ![A:$i,B:$i]:
% 0.60/0.84        ( ( v1_relat_1 @ B ) =>
% 0.60/0.84          ( ( k6_subset_1 @
% 0.60/0.84              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.60/0.84            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.60/0.84    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.60/0.84  thf('36', plain,
% 0.60/0.84      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.60/0.84         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.60/0.84         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.84  thf('38', plain,
% 0.60/0.84      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.60/0.84         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.60/0.84         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.60/0.84      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.60/0.84          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.60/0.84          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.60/0.84        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.84      inference('sup-', [status(thm)], ['35', '39'])).
% 0.60/0.84  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('42', plain,
% 0.60/0.84      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.60/0.84         (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.60/0.84         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.60/0.84      inference('demod', [status(thm)], ['40', '41'])).
% 0.60/0.84  thf('43', plain,
% 0.60/0.84      ((((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.60/0.84          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.60/0.84        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.84      inference('sup-', [status(thm)], ['6', '42'])).
% 0.60/0.84  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('45', plain,
% 0.60/0.84      (((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.60/0.84         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.60/0.84      inference('demod', [status(thm)], ['43', '44'])).
% 0.60/0.84  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
