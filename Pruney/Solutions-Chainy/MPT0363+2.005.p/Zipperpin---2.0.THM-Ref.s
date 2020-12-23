%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lqClm50W7T

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 287 expanded)
%              Number of leaves         :   31 ( 100 expanded)
%              Depth                    :   25
%              Number of atoms          :  847 (2233 expanded)
%              Number of equality atoms :   44 ( 101 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t43_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ C )
            <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X52 )
      | ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X56: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ ( k3_tarski @ X47 ) )
      | ~ ( r2_hidden @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X50: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X52 )
      | ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X56: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('20',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ ( k3_tarski @ X47 ) )
      | ~ ( r2_hidden @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('22',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X50: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('24',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k3_subset_1 @ X54 @ X55 )
        = ( k4_xboole_0 @ X54 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('41',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['8','9'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('51',plain,(
    r1_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('53',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
      = sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('67',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','68'])).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k4_xboole_0 @ X0 @ sk_B ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','71'])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('78',plain,
    ( ( ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_C @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('82',plain,
    ( ( ( k4_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
        | ( r1_xboole_0 @ X0 @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
        | ( r1_xboole_0 @ X0 @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','86'])).

thf('88',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lqClm50W7T
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:39 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 249 iterations in 0.097s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(t43_subset_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.21/0.55             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55          ( ![C:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.21/0.55                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.55        | ~ (r1_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.21/0.55       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d2_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X51 : $i, X52 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X51 @ X52)
% 0.21/0.55          | (r2_hidden @ X51 @ X52)
% 0.21/0.55          | (v1_xboole_0 @ X52))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf(fc1_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('5', plain, (![X56 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X56))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('6', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf(l49_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X46 : $i, X47 : $i]:
% 0.21/0.55         ((r1_tarski @ X46 @ (k3_tarski @ X47)) | ~ (r2_hidden @ X46 @ X47))),
% 0.21/0.55      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.55  thf('8', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf(t99_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.55  thf('9', plain, (![X50 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X50)) = (X50))),
% 0.21/0.55      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.55  thf('10', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.55        | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['11'])).
% 0.21/0.55  thf(t86_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.55       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X16 @ X17)
% 0.21/0.55          | ~ (r1_xboole_0 @ X16 @ X18)
% 0.21/0.55          | (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X18)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))
% 0.21/0.55           | ~ (r1_tarski @ sk_B @ X0)))
% 0.21/0.55         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.21/0.55         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.55  thf('16', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X51 : $i, X52 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X51 @ X52)
% 0.21/0.55          | (r2_hidden @ X51 @ X52)
% 0.21/0.55          | (v1_xboole_0 @ X52))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.55        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain, (![X56 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X56))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('20', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X46 : $i, X47 : $i]:
% 0.21/0.55         ((r1_tarski @ X46 @ (k3_tarski @ X47)) | ~ (r2_hidden @ X46 @ X47))),
% 0.21/0.55      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.55  thf('22', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain, (![X50 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X50)) = (X50))),
% 0.21/0.55      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.55  thf('24', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf(t28_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('26', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf(t100_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['26', '29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))
% 0.21/0.55         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '30'])).
% 0.21/0.55  thf('32', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d5_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X54 : $i, X55 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X54 @ X55) = (k4_xboole_0 @ X54 @ X55))
% 0.21/0.55          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X54)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['26', '29'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.21/0.55       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['31', '38'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.21/0.55       ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('split', [status(esa)], ['11'])).
% 0.21/0.55  thf('41', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf(l97_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('47', plain, ((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['43', '46'])).
% 0.21/0.55  thf('48', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('49', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('51', plain, ((r1_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('split', [status(esa)], ['11'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.55          = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.21/0.55          = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['52', '57'])).
% 0.21/0.55  thf(t21_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.21/0.55           = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.55  thf(t46_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.55  thf('63', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)) = (k1_xboole_0)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['58', '63'])).
% 0.21/0.55  thf(t84_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.21/0.55          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X13 @ X14)
% 0.21/0.55          | ~ (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.55          | ~ (r1_xboole_0 @ X13 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.21/0.55           | ~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.21/0.55           | (r1_xboole_0 @ X0 @ sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.55  thf('67', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.21/0.55           | (r1_xboole_0 @ X0 @ sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (((r1_xboole_0 @ sk_C @ sk_B))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['51', '68'])).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X16 @ X17)
% 0.21/0.55          | ~ (r1_xboole_0 @ X16 @ X18)
% 0.21/0.55          | (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X18)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          ((r1_tarski @ sk_C @ (k4_xboole_0 @ X0 @ sk_B))
% 0.21/0.55           | ~ (r1_tarski @ sk_C @ X0)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '71'])).
% 0.21/0.55  thf('73', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['73', '74'])).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      (((r1_tarski @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['72', '75'])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      ((((k3_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_C)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      ((((k4_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.21/0.55          = (k5_xboole_0 @ sk_C @ sk_C)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['78', '79'])).
% 0.21/0.55  thf('81', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      ((((k4_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.55  thf('83', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X13 @ X14)
% 0.21/0.55          | ~ (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.55          | ~ (r1_xboole_0 @ X13 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.21/0.55           | ~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.21/0.55           | (r1_xboole_0 @ X0 @ sk_C)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.55  thf('85', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.21/0.55           | (r1_xboole_0 @ X0 @ sk_C)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.55  thf('87', plain,
% 0.21/0.55      (((r1_xboole_0 @ sk_B @ sk_C))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['47', '86'])).
% 0.21/0.55  thf('88', plain,
% 0.21/0.55      ((~ (r1_xboole_0 @ sk_B @ sk_C)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.21/0.55       ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.55  thf('90', plain, ($false),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '89'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
