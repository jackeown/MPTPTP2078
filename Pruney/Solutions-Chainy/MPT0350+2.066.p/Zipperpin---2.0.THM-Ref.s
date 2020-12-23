%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Wo3vBSYkY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:54 EST 2020

% Result     : Theorem 3.51s
% Output     : Refutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 315 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  791 (2400 expanded)
%              Number of equality atoms :   80 ( 214 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X17: $i] :
      ( r1_tarski @ X17 @ X17 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ X67 )
      | ( r2_hidden @ X66 @ X67 )
      | ( v1_xboole_0 @ X67 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X74: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('13',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X62 @ X61 )
      | ( r1_tarski @ X62 @ X60 )
      | ( X61
       != ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r1_tarski @ X62 @ X60 )
      | ~ ( r2_hidden @ X62 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['7','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X23: $i] :
      ( r1_tarski @ k1_xboole_0 @ X23 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ k1_xboole_0 )
      = X29 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X70: $i,X71: $i] :
      ( ( ( k3_subset_1 @ X70 @ X71 )
        = ( k4_xboole_0 @ X70 @ X71 ) )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('59',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('62',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','43','44','62'])).

thf('64',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('65',plain,(
    ! [X69: $i] :
      ( ( k2_subset_1 @ X69 )
      = X69 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('66',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('68',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('70',plain,(
    ! [X72: $i,X73: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X72 @ X73 ) @ ( k1_zfmisc_1 @ X72 ) )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('71',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('73',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ X76 ) )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ X76 ) )
      | ( ( k4_subset_1 @ X76 @ X75 @ X77 )
        = ( k2_xboole_0 @ X75 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('76',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('77',plain,(
    ! [X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ X76 ) )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ X76 ) )
      | ( ( k4_subset_1 @ X76 @ X75 @ X77 )
        = ( k3_tarski @ ( k2_tarski @ X75 @ X77 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Wo3vBSYkY
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.51/3.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.51/3.72  % Solved by: fo/fo7.sh
% 3.51/3.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.51/3.72  % done 3146 iterations in 3.258s
% 3.51/3.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.51/3.72  % SZS output start Refutation
% 3.51/3.72  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.51/3.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.51/3.72  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.51/3.72  thf(sk_A_type, type, sk_A: $i).
% 3.51/3.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.51/3.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.51/3.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.51/3.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.51/3.72  thf(sk_B_type, type, sk_B: $i).
% 3.51/3.72  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.51/3.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.51/3.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.51/3.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.51/3.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.51/3.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.51/3.72  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.51/3.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.51/3.72  thf(d10_xboole_0, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.51/3.72  thf('0', plain,
% 3.51/3.72      (![X16 : $i, X17 : $i]: ((r1_tarski @ X16 @ X17) | ((X16) != (X17)))),
% 3.51/3.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.51/3.72  thf('1', plain, (![X17 : $i]: (r1_tarski @ X17 @ X17)),
% 3.51/3.72      inference('simplify', [status(thm)], ['0'])).
% 3.51/3.72  thf(t28_xboole_1, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.51/3.72  thf('2', plain,
% 3.51/3.72      (![X21 : $i, X22 : $i]:
% 3.51/3.72         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 3.51/3.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.51/3.72  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.51/3.72      inference('sup-', [status(thm)], ['1', '2'])).
% 3.51/3.72  thf(commutativity_k3_xboole_0, axiom,
% 3.51/3.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.51/3.72  thf('4', plain,
% 3.51/3.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.51/3.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.51/3.72  thf(t100_xboole_1, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.51/3.72  thf('5', plain,
% 3.51/3.72      (![X19 : $i, X20 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X19 @ X20)
% 3.51/3.72           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 3.51/3.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.51/3.72  thf('6', plain,
% 3.51/3.72      (![X0 : $i, X1 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X0 @ X1)
% 3.51/3.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.51/3.72      inference('sup+', [status(thm)], ['4', '5'])).
% 3.51/3.72  thf('7', plain,
% 3.51/3.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.51/3.72      inference('sup+', [status(thm)], ['3', '6'])).
% 3.51/3.72  thf(t25_subset_1, conjecture,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.51/3.72       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 3.51/3.72         ( k2_subset_1 @ A ) ) ))).
% 3.51/3.72  thf(zf_stmt_0, negated_conjecture,
% 3.51/3.72    (~( ![A:$i,B:$i]:
% 3.51/3.72        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.51/3.72          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 3.51/3.72            ( k2_subset_1 @ A ) ) ) )),
% 3.51/3.72    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 3.51/3.72  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.51/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.72  thf(d2_subset_1, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( ( v1_xboole_0 @ A ) =>
% 3.51/3.72         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.51/3.72       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.51/3.72         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.51/3.72  thf('9', plain,
% 3.51/3.72      (![X66 : $i, X67 : $i]:
% 3.51/3.72         (~ (m1_subset_1 @ X66 @ X67)
% 3.51/3.72          | (r2_hidden @ X66 @ X67)
% 3.51/3.72          | (v1_xboole_0 @ X67))),
% 3.51/3.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.51/3.72  thf('10', plain,
% 3.51/3.72      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.51/3.72        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 3.51/3.72      inference('sup-', [status(thm)], ['8', '9'])).
% 3.51/3.72  thf(fc1_subset_1, axiom,
% 3.51/3.72    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.51/3.72  thf('11', plain, (![X74 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X74))),
% 3.51/3.72      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.51/3.72  thf('12', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.51/3.72      inference('clc', [status(thm)], ['10', '11'])).
% 3.51/3.72  thf(d1_zfmisc_1, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 3.51/3.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 3.51/3.72  thf('13', plain,
% 3.51/3.72      (![X60 : $i, X61 : $i, X62 : $i]:
% 3.51/3.72         (~ (r2_hidden @ X62 @ X61)
% 3.51/3.72          | (r1_tarski @ X62 @ X60)
% 3.51/3.72          | ((X61) != (k1_zfmisc_1 @ X60)))),
% 3.51/3.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 3.51/3.72  thf('14', plain,
% 3.51/3.72      (![X60 : $i, X62 : $i]:
% 3.51/3.72         ((r1_tarski @ X62 @ X60) | ~ (r2_hidden @ X62 @ (k1_zfmisc_1 @ X60)))),
% 3.51/3.72      inference('simplify', [status(thm)], ['13'])).
% 3.51/3.72  thf('15', plain, ((r1_tarski @ sk_B @ sk_A)),
% 3.51/3.72      inference('sup-', [status(thm)], ['12', '14'])).
% 3.51/3.72  thf('16', plain,
% 3.51/3.72      (![X21 : $i, X22 : $i]:
% 3.51/3.72         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 3.51/3.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.51/3.72  thf('17', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 3.51/3.72      inference('sup-', [status(thm)], ['15', '16'])).
% 3.51/3.72  thf('18', plain,
% 3.51/3.72      (![X0 : $i, X1 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X0 @ X1)
% 3.51/3.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.51/3.72      inference('sup+', [status(thm)], ['4', '5'])).
% 3.51/3.72  thf('19', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup+', [status(thm)], ['17', '18'])).
% 3.51/3.72  thf(t48_xboole_1, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.51/3.72  thf('20', plain,
% 3.51/3.72      (![X24 : $i, X25 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 3.51/3.72           = (k3_xboole_0 @ X24 @ X25))),
% 3.51/3.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.51/3.72  thf('21', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 3.51/3.72         = (k3_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup+', [status(thm)], ['19', '20'])).
% 3.51/3.72  thf('22', plain,
% 3.51/3.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.51/3.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.51/3.72  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 3.51/3.72      inference('sup-', [status(thm)], ['15', '16'])).
% 3.51/3.72  thf('24', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 3.51/3.72      inference('demod', [status(thm)], ['21', '22', '23'])).
% 3.51/3.72  thf(t52_xboole_1, axiom,
% 3.51/3.72    (![A:$i,B:$i,C:$i]:
% 3.51/3.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 3.51/3.72       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 3.51/3.72  thf('25', plain,
% 3.51/3.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 3.51/3.72           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ 
% 3.51/3.72              (k3_xboole_0 @ X26 @ X28)))),
% 3.51/3.72      inference('cnf', [status(esa)], [t52_xboole_1])).
% 3.51/3.72  thf(l51_zfmisc_1, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.51/3.72  thf('26', plain,
% 3.51/3.72      (![X64 : $i, X65 : $i]:
% 3.51/3.72         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.51/3.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.51/3.72  thf('27', plain,
% 3.51/3.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 3.51/3.72           = (k3_tarski @ 
% 3.51/3.72              (k2_tarski @ (k4_xboole_0 @ X26 @ X27) @ 
% 3.51/3.72               (k3_xboole_0 @ X26 @ X28))))),
% 3.51/3.72      inference('demod', [status(thm)], ['25', '26'])).
% 3.51/3.72  thf('28', plain,
% 3.51/3.72      (![X0 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ sk_A @ 
% 3.51/3.72           (k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ X0))
% 3.51/3.72           = (k3_tarski @ (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ X0))))),
% 3.51/3.72      inference('sup+', [status(thm)], ['24', '27'])).
% 3.51/3.72  thf('29', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ 
% 3.51/3.72         (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 3.51/3.72          (k5_xboole_0 @ sk_A @ sk_B)))
% 3.51/3.72         = (k3_tarski @ 
% 3.51/3.72            (k2_tarski @ sk_B @ 
% 3.51/3.72             (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)))))),
% 3.51/3.72      inference('sup+', [status(thm)], ['7', '28'])).
% 3.51/3.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.51/3.72  thf('30', plain, (![X23 : $i]: (r1_tarski @ k1_xboole_0 @ X23)),
% 3.51/3.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.51/3.72  thf('31', plain,
% 3.51/3.72      (![X21 : $i, X22 : $i]:
% 3.51/3.72         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 3.51/3.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.51/3.72  thf('32', plain,
% 3.51/3.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.51/3.72      inference('sup-', [status(thm)], ['30', '31'])).
% 3.51/3.72  thf('33', plain,
% 3.51/3.72      (![X0 : $i, X1 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X0 @ X1)
% 3.51/3.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.51/3.72      inference('sup+', [status(thm)], ['4', '5'])).
% 3.51/3.72  thf('34', plain,
% 3.51/3.72      (![X0 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.51/3.72      inference('sup+', [status(thm)], ['32', '33'])).
% 3.51/3.72  thf(t5_boole, axiom,
% 3.51/3.72    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.51/3.72  thf('35', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ k1_xboole_0) = (X29))),
% 3.51/3.72      inference('cnf', [status(esa)], [t5_boole])).
% 3.51/3.72  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.51/3.72      inference('demod', [status(thm)], ['34', '35'])).
% 3.51/3.72  thf('37', plain,
% 3.51/3.72      (![X24 : $i, X25 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 3.51/3.72           = (k3_xboole_0 @ X24 @ X25))),
% 3.51/3.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.51/3.72  thf('38', plain,
% 3.51/3.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.51/3.72      inference('sup+', [status(thm)], ['36', '37'])).
% 3.51/3.72  thf('39', plain,
% 3.51/3.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.51/3.72      inference('sup+', [status(thm)], ['3', '6'])).
% 3.51/3.72  thf('40', plain,
% 3.51/3.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.51/3.72      inference('sup-', [status(thm)], ['30', '31'])).
% 3.51/3.72  thf('41', plain,
% 3.51/3.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.51/3.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.51/3.72  thf('42', plain,
% 3.51/3.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.72      inference('sup+', [status(thm)], ['40', '41'])).
% 3.51/3.72  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.51/3.72      inference('demod', [status(thm)], ['38', '39', '42'])).
% 3.51/3.72  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.51/3.72      inference('demod', [status(thm)], ['34', '35'])).
% 3.51/3.72  thf('45', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.51/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.72  thf(d5_subset_1, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.51/3.72       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.51/3.72  thf('46', plain,
% 3.51/3.72      (![X70 : $i, X71 : $i]:
% 3.51/3.72         (((k3_subset_1 @ X70 @ X71) = (k4_xboole_0 @ X70 @ X71))
% 3.51/3.72          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ X70)))),
% 3.51/3.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.51/3.72  thf('47', plain,
% 3.51/3.72      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup-', [status(thm)], ['45', '46'])).
% 3.51/3.72  thf('48', plain,
% 3.51/3.72      (![X24 : $i, X25 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 3.51/3.72           = (k3_xboole_0 @ X24 @ X25))),
% 3.51/3.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.51/3.72  thf('49', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 3.51/3.72         = (k3_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup+', [status(thm)], ['47', '48'])).
% 3.51/3.72  thf('50', plain,
% 3.51/3.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.51/3.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.51/3.72  thf('51', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 3.51/3.72         = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.51/3.72      inference('demod', [status(thm)], ['49', '50'])).
% 3.51/3.72  thf('52', plain,
% 3.51/3.72      (![X24 : $i, X25 : $i]:
% 3.51/3.72         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 3.51/3.72           = (k3_xboole_0 @ X24 @ X25))),
% 3.51/3.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.51/3.72  thf('53', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 3.51/3.72         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 3.51/3.72      inference('sup+', [status(thm)], ['51', '52'])).
% 3.51/3.72  thf('54', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 3.51/3.72      inference('sup-', [status(thm)], ['15', '16'])).
% 3.51/3.72  thf('55', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ sk_B)
% 3.51/3.72         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 3.51/3.72      inference('demod', [status(thm)], ['53', '54'])).
% 3.51/3.72  thf('56', plain,
% 3.51/3.72      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup-', [status(thm)], ['45', '46'])).
% 3.51/3.72  thf('57', plain,
% 3.51/3.72      (((k3_subset_1 @ sk_A @ sk_B)
% 3.51/3.72         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 3.51/3.72      inference('demod', [status(thm)], ['55', '56'])).
% 3.51/3.72  thf('58', plain,
% 3.51/3.72      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup+', [status(thm)], ['17', '18'])).
% 3.51/3.72  thf('59', plain,
% 3.51/3.72      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup-', [status(thm)], ['45', '46'])).
% 3.51/3.72  thf('60', plain,
% 3.51/3.72      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup+', [status(thm)], ['58', '59'])).
% 3.51/3.72  thf('61', plain,
% 3.51/3.72      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup+', [status(thm)], ['58', '59'])).
% 3.51/3.72  thf('62', plain,
% 3.51/3.72      (((k5_xboole_0 @ sk_A @ sk_B)
% 3.51/3.72         = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 3.51/3.72      inference('demod', [status(thm)], ['57', '60', '61'])).
% 3.51/3.72  thf('63', plain,
% 3.51/3.72      (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))))),
% 3.51/3.72      inference('demod', [status(thm)], ['29', '43', '44', '62'])).
% 3.51/3.72  thf('64', plain,
% 3.51/3.72      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 3.51/3.72         != (k2_subset_1 @ sk_A))),
% 3.51/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.72  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.51/3.72  thf('65', plain, (![X69 : $i]: ((k2_subset_1 @ X69) = (X69))),
% 3.51/3.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.51/3.72  thf('66', plain,
% 3.51/3.72      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 3.51/3.72      inference('demod', [status(thm)], ['64', '65'])).
% 3.51/3.72  thf('67', plain,
% 3.51/3.72      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup+', [status(thm)], ['58', '59'])).
% 3.51/3.72  thf('68', plain,
% 3.51/3.72      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 3.51/3.72      inference('demod', [status(thm)], ['66', '67'])).
% 3.51/3.72  thf('69', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.51/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.72  thf(dt_k3_subset_1, axiom,
% 3.51/3.72    (![A:$i,B:$i]:
% 3.51/3.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.51/3.72       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.51/3.72  thf('70', plain,
% 3.51/3.72      (![X72 : $i, X73 : $i]:
% 3.51/3.72         ((m1_subset_1 @ (k3_subset_1 @ X72 @ X73) @ (k1_zfmisc_1 @ X72))
% 3.51/3.72          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ X72)))),
% 3.51/3.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.51/3.72  thf('71', plain,
% 3.51/3.72      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 3.51/3.72      inference('sup-', [status(thm)], ['69', '70'])).
% 3.51/3.72  thf('72', plain,
% 3.51/3.72      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.51/3.72      inference('sup+', [status(thm)], ['58', '59'])).
% 3.51/3.72  thf('73', plain,
% 3.51/3.72      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 3.51/3.72      inference('demod', [status(thm)], ['71', '72'])).
% 3.51/3.72  thf('74', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.51/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.72  thf(redefinition_k4_subset_1, axiom,
% 3.51/3.72    (![A:$i,B:$i,C:$i]:
% 3.51/3.72     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.51/3.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.51/3.72       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.51/3.72  thf('75', plain,
% 3.51/3.72      (![X75 : $i, X76 : $i, X77 : $i]:
% 3.51/3.72         (~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ X76))
% 3.51/3.72          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ X76))
% 3.51/3.72          | ((k4_subset_1 @ X76 @ X75 @ X77) = (k2_xboole_0 @ X75 @ X77)))),
% 3.51/3.72      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.51/3.72  thf('76', plain,
% 3.51/3.72      (![X64 : $i, X65 : $i]:
% 3.51/3.72         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.51/3.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.51/3.72  thf('77', plain,
% 3.51/3.72      (![X75 : $i, X76 : $i, X77 : $i]:
% 3.51/3.72         (~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ X76))
% 3.51/3.72          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ X76))
% 3.51/3.72          | ((k4_subset_1 @ X76 @ X75 @ X77)
% 3.51/3.72              = (k3_tarski @ (k2_tarski @ X75 @ X77))))),
% 3.51/3.72      inference('demod', [status(thm)], ['75', '76'])).
% 3.51/3.72  thf('78', plain,
% 3.51/3.72      (![X0 : $i]:
% 3.51/3.72         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 3.51/3.72            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 3.51/3.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 3.51/3.72      inference('sup-', [status(thm)], ['74', '77'])).
% 3.51/3.72  thf('79', plain,
% 3.51/3.72      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 3.51/3.72         = (k3_tarski @ (k2_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))))),
% 3.51/3.72      inference('sup-', [status(thm)], ['73', '78'])).
% 3.51/3.72  thf('80', plain,
% 3.51/3.72      (((k3_tarski @ (k2_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))
% 3.51/3.72         != (sk_A))),
% 3.51/3.72      inference('demod', [status(thm)], ['68', '79'])).
% 3.51/3.72  thf('81', plain, ($false),
% 3.51/3.72      inference('simplify_reflect-', [status(thm)], ['63', '80'])).
% 3.51/3.72  
% 3.51/3.72  % SZS output end Refutation
% 3.51/3.72  
% 3.51/3.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
