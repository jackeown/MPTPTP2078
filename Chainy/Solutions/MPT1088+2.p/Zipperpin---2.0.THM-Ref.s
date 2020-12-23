%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1088+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ge4AxGpVPp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   16 (  18 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :   53 (  65 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_A_17_type,type,(
    sk_A_17: $i )).

thf(sk_B_100_type,type,(
    sk_B_100: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(fc12_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5691: $i,X5692: $i] :
      ( ~ ( v1_finset_1 @ X5691 )
      | ( v1_finset_1 @ ( k4_xboole_0 @ ( X5691 @ X5692 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc12_finset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X5691: $i,X5692: $i] :
      ( ~ ( v1_finset_1 @ X5691 )
      | ( v1_finset_1 @ ( k6_subset_1 @ ( X5691 @ X5692 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t16_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k6_subset_1 @ ( A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_finset_1 @ A )
       => ( v1_finset_1 @ ( k6_subset_1 @ ( A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_finset_1])).

thf('3',plain,(
    ~ ( v1_finset_1 @ ( k6_subset_1 @ ( sk_A_17 @ sk_B_100 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( v1_finset_1 @ sk_A_17 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_finset_1 @ sk_A_17 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['4','5'])).

%------------------------------------------------------------------------------
