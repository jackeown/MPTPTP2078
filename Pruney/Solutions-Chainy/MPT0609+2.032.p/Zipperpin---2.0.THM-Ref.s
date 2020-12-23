%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W4wyOOludw

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:03 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 127 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :   21
%              Number of atoms          :  637 (1223 expanded)
%              Number of equality atoms :   49 (  99 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X18 @ ( k7_relat_1 @ X18 @ X19 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X18 @ ( k7_relat_1 @ X18 @ X19 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k7_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) )
        = ( k7_relat_1 @ X17 @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ ( k1_relat_1 @ X17 ) ) ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X18 @ ( k7_relat_1 @ X18 @ X19 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k7_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) )
        = ( k7_relat_1 @ X17 @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ ( k1_relat_1 @ X17 ) ) ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X18 @ ( k7_relat_1 @ X18 @ X19 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k4_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k4_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','34'])).

thf('36',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','38'])).

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

thf('40',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W4wyOOludw
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 259 iterations in 0.211s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(t212_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.45/0.66         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k6_subset_1 @ X18 @ (k7_relat_1 @ X18 @ X19)))
% 0.45/0.66            = (k6_subset_1 @ (k1_relat_1 @ X18) @ X19))
% 0.45/0.66          | ~ (v1_relat_1 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.45/0.66  thf(redefinition_k6_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k4_xboole_0 @ X18 @ (k7_relat_1 @ X18 @ X19)))
% 0.45/0.66            = (k4_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.45/0.66          | ~ (v1_relat_1 @ X18))),
% 0.45/0.66      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.45/0.66  thf(t71_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.45/0.66       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.66  thf('4', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.66  thf(t189_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( v1_relat_1 @ B ) =>
% 0.45/0.66           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.45/0.66             ( k7_relat_1 @
% 0.45/0.66               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X16)
% 0.45/0.66          | ((k7_relat_1 @ X17 @ (k1_relat_1 @ X16))
% 0.45/0.66              = (k7_relat_1 @ X17 @ 
% 0.45/0.66                 (k1_relat_1 @ (k7_relat_1 @ X16 @ (k1_relat_1 @ X17)))))
% 0.45/0.66          | ~ (v1_relat_1 @ X17))),
% 0.45/0.66      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.45/0.66  thf(t87_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X22 : $i, X23 : $i]:
% 0.45/0.66         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X23)) @ X23)
% 0.45/0.66          | ~ (v1_relat_1 @ X22))),
% 0.45/0.66      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.45/0.66  thf(t91_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.45/0.66         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X24 : $i, X25 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X24 @ (k1_relat_1 @ X25))
% 0.45/0.66          | ((k1_relat_1 @ (k7_relat_1 @ X25 @ X24)) = (X24))
% 0.45/0.66          | ~ (v1_relat_1 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k1_relat_1 @ 
% 0.45/0.66              (k7_relat_1 @ X0 @ 
% 0.45/0.66               (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))
% 0.45/0.66              = (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.45/0.66            = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['5', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.45/0.66              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.66            = (k1_relat_1 @ 
% 0.45/0.66               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['4', '10'])).
% 0.45/0.66  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.45/0.66  thf('12', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.66            = (k1_relat_1 @ 
% 0.45/0.66               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k4_xboole_0 @ X18 @ (k7_relat_1 @ X18 @ X19)))
% 0.45/0.66            = (k4_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.45/0.66          | ~ (v1_relat_1 @ X18))),
% 0.45/0.66      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.45/0.66  thf('15', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.66            = (k1_relat_1 @ 
% 0.45/0.66               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.66            = (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.66           = (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.66            = (k1_relat_1 @ 
% 0.45/0.66               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X16)
% 0.45/0.66          | ((k7_relat_1 @ X17 @ (k1_relat_1 @ X16))
% 0.45/0.66              = (k7_relat_1 @ X17 @ 
% 0.45/0.66                 (k1_relat_1 @ (k7_relat_1 @ X16 @ (k1_relat_1 @ X17)))))
% 0.45/0.66          | ~ (v1_relat_1 @ X17))),
% 0.45/0.66      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k7_relat_1 @ X1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.45/0.66            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.66  thf('24', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k7_relat_1 @ X1 @ X0)
% 0.45/0.66            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X1)
% 0.45/0.66          | ((k7_relat_1 @ X1 @ X0)
% 0.45/0.66              = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.45/0.66            = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.45/0.66               (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['19', '26'])).
% 0.45/0.66  thf('28', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.45/0.66           = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.45/0.66              (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 0.45/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i]:
% 0.45/0.66         (((k1_relat_1 @ (k4_xboole_0 @ X18 @ (k7_relat_1 @ X18 @ X19)))
% 0.45/0.66            = (k4_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.45/0.66          | ~ (v1_relat_1 @ X18))),
% 0.45/0.66      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_relat_1 @ 
% 0.45/0.66            (k4_xboole_0 @ (k6_relat_1 @ X1) @ 
% 0.45/0.66             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.45/0.66            = (k4_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ 
% 0.45/0.66               (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.66  thf('33', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relat_1 @ 
% 0.45/0.66           (k4_xboole_0 @ (k6_relat_1 @ X1) @ 
% 0.45/0.66            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.45/0.66           = (k4_xboole_0 @ X1 @ 
% 0.45/0.66              (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.45/0.66      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k4_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)
% 0.45/0.66            = (k4_xboole_0 @ X1 @ 
% 0.45/0.66               (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['14', '34'])).
% 0.45/0.66  thf('36', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.66  thf('37', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X1 @ X0)
% 0.45/0.66           = (k4_xboole_0 @ X1 @ 
% 0.45/0.66              (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.45/0.66      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.45/0.66            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.45/0.66               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['13', '38'])).
% 0.45/0.66  thf(t213_relat_1, conjecture,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( k6_subset_1 @
% 0.45/0.66           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.45/0.66         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i]:
% 0.45/0.66        ( ( v1_relat_1 @ B ) =>
% 0.45/0.66          ( ( k6_subset_1 @
% 0.45/0.66              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.45/0.66            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.45/0.66         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.45/0.66         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.45/0.66         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.45/0.66         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.45/0.66      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.66          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['39', '43'])).
% 0.45/0.66  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.66         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.45/0.66      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.66          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '46'])).
% 0.45/0.66  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.66         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
