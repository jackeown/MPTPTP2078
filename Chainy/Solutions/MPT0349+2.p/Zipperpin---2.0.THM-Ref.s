%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0349+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NxLDUmSsUo

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  123 ( 129 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t22_subset_1,conjecture,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ ( A @ ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k2_subset_1 @ A )
        = ( k3_subset_1 @ ( A @ ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_subset_1])).

thf('0',plain,(
    ( k2_subset_1 @ sk_A_2 )
 != ( k3_subset_1 @ ( sk_A_2 @ ( k1_subset_1 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X1470: $i] :
      ( ( k2_subset_1 @ X1470 )
      = X1470 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X1469: $i] :
      ( ( k1_subset_1 @ X1469 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X1469: $i] :
      ( ( k1_subset_1 @ X1469 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A_2
 != ( k3_subset_1 @ ( sk_A_2 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','1','4'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X1535: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ X1535 ) ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X1535: $i] :
      ( m1_subset_1 @ ( o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X1535 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1471: $i,X1472: $i] :
      ( ( ( k3_subset_1 @ ( X1471 @ X1472 ) )
        = ( k4_xboole_0 @ ( X1471 @ X1472 ) ) )
      | ~ ( m1_subset_1 @ ( X1472 @ ( k1_zfmisc_1 @ X1471 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ o_0_0_xboole_0 ) )
      = ( k4_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('11',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ k1_xboole_0 ) )
      = X244 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ o_0_0_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_A_2 != sk_A_2 ),
    inference(demod,[status(thm)],['5','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
