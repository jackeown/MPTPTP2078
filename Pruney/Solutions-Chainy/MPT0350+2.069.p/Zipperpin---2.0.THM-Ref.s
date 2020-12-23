%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ymflVQ9JQb

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 241 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  869 (1900 expanded)
%              Number of equality atoms :   83 ( 160 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( r1_tarski @ X28 @ X26 )
      | ( X27
       != ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X27 )
      | ( X27
       != ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( m1_subset_1 @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['15','26'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( sk_A
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_A
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('57',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['58','75'])).

thf('77',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('78',plain,(
    ! [X35: $i] :
      ( ( k2_subset_1 @ X35 )
      = X35 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('79',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('81',plain,(
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('82',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('84',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k4_subset_1 @ X42 @ X41 @ X43 )
        = ( k2_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['79','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ymflVQ9JQb
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 305 iterations in 0.098s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(t25_subset_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.55         ( k2_subset_1 @ A ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.55            ( k2_subset_1 @ A ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.21/0.55  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d5_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X36 : $i, X37 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.21/0.55          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d2_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X32 : $i, X33 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X32 @ X33)
% 0.21/0.55          | (r2_hidden @ X32 @ X33)
% 0.21/0.55          | (v1_xboole_0 @ X33))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf(fc1_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('6', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('7', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf(d1_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X28 @ X27)
% 0.21/0.55          | (r1_tarski @ X28 @ X26)
% 0.21/0.55          | ((X27) != (k1_zfmisc_1 @ X26)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X26 : $i, X28 : $i]:
% 0.21/0.55         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.55  thf('10', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.55  thf(t28_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf(t49_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.21/0.55       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.55           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.21/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k4_xboole_0 @ sk_B @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['2', '14'])).
% 0.21/0.55  thf(d10_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.55  thf('17', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X25 @ X26)
% 0.21/0.55          | (r2_hidden @ X25 @ X27)
% 0.21/0.55          | ((X27) != (k1_zfmisc_1 @ X26)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X25 : $i, X26 : $i]:
% 0.21/0.55         ((r2_hidden @ X25 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X25 @ X26))),
% 0.21/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.55  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X32 : $i, X33 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X32 @ X33)
% 0.21/0.55          | (m1_subset_1 @ X32 @ X33)
% 0.21/0.55          | (v1_xboole_0 @ X33))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.21/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('24', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X36 : $i, X37 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.21/0.55          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k3_subset_1 @ sk_B @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '26'])).
% 0.21/0.55  thf(t94_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ A @ B ) =
% 0.21/0.55       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X16 @ X17)
% 0.21/0.55           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.21/0.55              (k3_xboole_0 @ X16 @ X17)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.21/0.55            (k3_subset_1 @ sk_B @ sk_B)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf(t48_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.55           = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.55           = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('36', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('38', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.55           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.55           = (k4_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['35', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.55           = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X16 @ X17)
% 0.21/0.55           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.21/0.55              (k3_xboole_0 @ X16 @ X17)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.55              (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.55  thf(t22_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.21/0.55  thf(t100_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X5 @ X6)
% 0.21/0.55           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((X1)
% 0.21/0.55           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (((sk_A)
% 0.21/0.55         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.21/0.55            (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['34', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.55           = (k4_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (((sk_A)
% 0.21/0.55         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.21/0.55            (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['49', '54'])).
% 0.21/0.55  thf('56', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['29', '57'])).
% 0.21/0.55  thf('59', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X5 @ X6)
% 0.21/0.55           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X5 @ X6)
% 0.21/0.55           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55           = (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['59', '64'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_B @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.55  thf(t98_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X18 @ X19)
% 0.21/0.55           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.55         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['67', '68'])).
% 0.21/0.55  thf('70', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['71', '72'])).
% 0.21/0.55  thf('74', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['70', '73'])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      (((sk_A) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['69', '74'])).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['58', '75'])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         != (k2_subset_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.55  thf('78', plain, (![X35 : $i]: ((k2_subset_1 @ X35) = (X35))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.55  thf('80', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_k3_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (![X38 : $i, X39 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k3_subset_1 @ X38 @ X39) @ (k1_zfmisc_1 @ X38))
% 0.21/0.55          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.55  thf('83', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.21/0.55          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42))
% 0.21/0.55          | ((k4_subset_1 @ X42 @ X41 @ X43) = (k2_xboole_0 @ X41 @ X43)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['82', '85'])).
% 0.21/0.55  thf('87', plain,
% 0.21/0.55      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['79', '86'])).
% 0.21/0.55  thf('88', plain, ($false),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['76', '87'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
