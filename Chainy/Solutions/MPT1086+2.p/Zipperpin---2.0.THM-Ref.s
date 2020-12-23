%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1086+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sOrXDcdlcb

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   13 (  17 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    4
%              Number of atoms          :   45 (  77 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_100_type,type,(
    sk_B_100: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_A_17_type,type,(
    sk_A_17: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(fc9_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_finset_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5687: $i,X5688: $i] :
      ( ~ ( v1_finset_1 @ X5687 )
      | ~ ( v1_finset_1 @ X5688 )
      | ( v1_finset_1 @ ( k2_xboole_0 @ ( X5687 @ X5688 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc9_finset_1])).

thf(t14_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_finset_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_finset_1 @ A )
          & ( v1_finset_1 @ B ) )
       => ( v1_finset_1 @ ( k2_xboole_0 @ ( A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_finset_1])).

thf('1',plain,(
    ~ ( v1_finset_1 @ ( k2_xboole_0 @ ( sk_A_17 @ sk_B_100 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v1_finset_1 @ sk_B_100 )
    | ~ ( v1_finset_1 @ sk_A_17 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_finset_1 @ sk_B_100 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_finset_1 @ sk_A_17 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    $false ),
    inference(demod,[status(thm)],['2','3','4'])).

%------------------------------------------------------------------------------
