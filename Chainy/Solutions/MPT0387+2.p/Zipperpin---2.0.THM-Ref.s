%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0387+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OaeJkEZAFc

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  137 ( 167 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t5_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r2_hidden @ ( k1_xboole_0 @ A ) )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r2_hidden @ ( k1_xboole_0 @ A ) )
       => ( ( k1_setfam_1 @ A )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t5_setfam_1])).

thf('0',plain,(
    r2_hidden @ ( k1_xboole_0 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    r2_hidden @ ( o_0_0_xboole_0 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X1827: $i,X1828: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X1827 @ X1828 ) )
      | ~ ( r2_hidden @ ( X1828 @ X1827 ) ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('4',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_A_2 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( k6_subset_1 @ ( k1_setfam_1 @ sk_A_2 @ o_0_0_xboole_0 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('10',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ k1_xboole_0 ) )
      = X244 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X244: $i] :
      ( ( k6_subset_1 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_setfam_1 @ sk_A_2 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ( k1_setfam_1 @ sk_A_2 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ( k1_setfam_1 @ sk_A_2 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','18'])).

%------------------------------------------------------------------------------
