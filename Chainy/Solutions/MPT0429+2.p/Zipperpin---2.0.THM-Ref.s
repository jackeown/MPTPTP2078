%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0429+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0kDGJy1n8g

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 31.78s
% Output     : Refutation 31.78s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  239 ( 262 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_4_type,type,(
    sk_A_4: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t61_setfam_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_setfam_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_4 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_4 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k2_tarski @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_4 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ ( A @ ( A @ B ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X871: $i,X872: $i] :
      ( ( k1_enumset1 @ ( X871 @ ( X871 @ X872 ) ) )
      = ( k2_tarski @ ( X871 @ X872 ) ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ~ ( m1_subset_1 @ ( k1_enumset1 @ ( o_0_0_xboole_0 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_4 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X1729: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ X1729 ) ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X1729: $i] :
      ( m1_subset_1 @ ( o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X1729 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ A ) )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X1742: $i,X1743: $i] :
      ( ( X1742 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( X1743 @ X1742 ) )
      | ( m1_subset_1 @ ( k1_tarski @ X1743 @ ( k1_zfmisc_1 @ X1742 ) ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ! [X1742: $i,X1743: $i] :
      ( ( X1742 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ ( X1743 @ X1742 ) )
      | ( m1_subset_1 @ ( k1_tarski @ X1743 @ ( k1_zfmisc_1 @ X1742 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tarski @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X871: $i,X872: $i] :
      ( ( k1_enumset1 @ ( X871 @ ( X871 @ X872 ) ) )
      = ( k2_tarski @ ( X871 @ X872 ) ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_enumset1 @ ( o_0_0_xboole_0 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X1419: $i] :
      ( r1_tarski @ ( k1_tarski @ X1419 @ ( k1_zfmisc_1 @ X1419 ) ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('19',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 @ ( k1_zfmisc_1 @ X0 ) ) )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
     != k1_xboole_0 ) )).

thf('21',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('22',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('23',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_zfmisc_1 @ X0 )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_enumset1 @ ( o_0_0_xboole_0 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['6','25'])).

%------------------------------------------------------------------------------
