%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0341+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8qXUvfhPZN

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :   52 (  55 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t4_subset_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_subset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ~ ( m1_subset_1 @ ( o_0_0_xboole_0 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X1458: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X1458 @ ( k1_zfmisc_1 @ X1458 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X1457: $i] :
      ( ( k1_subset_1 @ X1457 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X1457: $i] :
      ( ( k1_subset_1 @ X1457 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X1458: $i] :
      ( m1_subset_1 @ ( o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X1458 ) ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['2','7'])).

%------------------------------------------------------------------------------
