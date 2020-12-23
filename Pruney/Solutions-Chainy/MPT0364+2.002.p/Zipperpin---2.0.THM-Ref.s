%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6b71thuot0

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:02 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 223 expanded)
%              Number of leaves         :   31 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  643 (1897 expanded)
%              Number of equality atoms :   32 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X23 @ X24 ) @ X24 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ sk_C_2 )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k6_subset_1 @ X0 @ sk_C_2 ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k6_subset_1 @ X0 @ sk_C_2 ) )
   <= ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k6_subset_1 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k6_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k6_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','22','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('32',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X41: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('35',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r1_tarski @ X30 @ X28 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('37',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['35','37'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k6_subset_1 @ X44 @ X45 )
      = ( k4_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['30','46'])).

thf('48',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X39: $i,X40: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('50',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('51',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_xboole_0 @ X48 @ X46 )
      | ( r1_tarski @ X48 @ ( k3_subset_1 @ X47 @ X46 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('54',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k3_subset_1 @ X43 @ ( k3_subset_1 @ X43 @ X42 ) )
        = X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k6_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('59',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_2 )
      | ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('61',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['24','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6b71thuot0
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 1.60/1.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.60/1.79  % Solved by: fo/fo7.sh
% 1.60/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.79  % done 3546 iterations in 1.344s
% 1.60/1.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.60/1.79  % SZS output start Refutation
% 1.60/1.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.60/1.79  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.60/1.79  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.60/1.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.60/1.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.60/1.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.60/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.79  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.60/1.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.60/1.79  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.60/1.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.60/1.79  thf(t44_subset_1, conjecture,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79       ( ![C:$i]:
% 1.60/1.79         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 1.60/1.79             ( r1_tarski @ B @ C ) ) ) ) ))).
% 1.60/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.79    (~( ![A:$i,B:$i]:
% 1.60/1.79        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79          ( ![C:$i]:
% 1.60/1.79            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 1.60/1.79                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 1.60/1.79    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 1.60/1.79  thf('0', plain,
% 1.60/1.79      ((~ (r1_tarski @ sk_B @ sk_C_2)
% 1.60/1.79        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('1', plain,
% 1.60/1.79      ((~ (r1_tarski @ sk_B @ sk_C_2)) <= (~ ((r1_tarski @ sk_B @ sk_C_2)))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('2', plain,
% 1.60/1.79      (~ ((r1_tarski @ sk_B @ sk_C_2)) | 
% 1.60/1.79       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf(t79_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.60/1.79  thf('3', plain,
% 1.60/1.79      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 1.60/1.79      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.60/1.79  thf(redefinition_k6_subset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.60/1.79  thf('4', plain,
% 1.60/1.79      (![X44 : $i, X45 : $i]:
% 1.60/1.79         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.60/1.79  thf('5', plain,
% 1.60/1.79      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X23 @ X24) @ X24)),
% 1.60/1.79      inference('demod', [status(thm)], ['3', '4'])).
% 1.60/1.79  thf('6', plain,
% 1.60/1.79      (((r1_tarski @ sk_B @ sk_C_2)
% 1.60/1.79        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('7', plain,
% 1.60/1.79      (((r1_tarski @ sk_B @ sk_C_2)) <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 1.60/1.79      inference('split', [status(esa)], ['6'])).
% 1.60/1.79  thf(t12_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.60/1.79  thf('8', plain,
% 1.60/1.79      (![X12 : $i, X13 : $i]:
% 1.60/1.79         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.60/1.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.60/1.79  thf('9', plain,
% 1.60/1.79      ((((k2_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)))
% 1.60/1.79         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['7', '8'])).
% 1.60/1.79  thf(t70_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.60/1.79            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.60/1.79       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.60/1.79            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.60/1.79  thf('10', plain,
% 1.60/1.79      (![X16 : $i, X17 : $i, X19 : $i]:
% 1.60/1.79         ((r1_xboole_0 @ X16 @ X17)
% 1.60/1.79          | ~ (r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X19)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.60/1.79  thf('11', plain,
% 1.60/1.79      ((![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_C_2) | (r1_xboole_0 @ X0 @ sk_B)))
% 1.60/1.79         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['9', '10'])).
% 1.60/1.79  thf('12', plain,
% 1.60/1.79      ((![X0 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X0 @ sk_C_2) @ sk_B))
% 1.60/1.79         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['5', '11'])).
% 1.60/1.79  thf(symmetry_r1_xboole_0, axiom,
% 1.60/1.79    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.60/1.79  thf('13', plain,
% 1.60/1.79      (![X8 : $i, X9 : $i]:
% 1.60/1.79         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 1.60/1.79      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.60/1.79  thf('14', plain,
% 1.60/1.79      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k6_subset_1 @ X0 @ sk_C_2)))
% 1.60/1.79         <= (((r1_tarski @ sk_B @ sk_C_2)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['12', '13'])).
% 1.60/1.79  thf('15', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(d5_subset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.60/1.79  thf('16', plain,
% 1.60/1.79      (![X37 : $i, X38 : $i]:
% 1.60/1.79         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 1.60/1.79          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 1.60/1.79      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.60/1.79  thf('17', plain,
% 1.60/1.79      (![X44 : $i, X45 : $i]:
% 1.60/1.79         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.60/1.79  thf('18', plain,
% 1.60/1.79      (![X37 : $i, X38 : $i]:
% 1.60/1.79         (((k3_subset_1 @ X37 @ X38) = (k6_subset_1 @ X37 @ X38))
% 1.60/1.79          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 1.60/1.79      inference('demod', [status(thm)], ['16', '17'])).
% 1.60/1.79  thf('19', plain,
% 1.60/1.79      (((k3_subset_1 @ sk_A @ sk_C_2) = (k6_subset_1 @ sk_A @ sk_C_2))),
% 1.60/1.79      inference('sup-', [status(thm)], ['15', '18'])).
% 1.60/1.79  thf('20', plain,
% 1.60/1.79      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 1.60/1.79         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))))),
% 1.60/1.79      inference('split', [status(esa)], ['0'])).
% 1.60/1.79  thf('21', plain,
% 1.60/1.79      ((~ (r1_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_C_2)))
% 1.60/1.79         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))))),
% 1.60/1.79      inference('sup-', [status(thm)], ['19', '20'])).
% 1.60/1.79  thf('22', plain,
% 1.60/1.79      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))) | 
% 1.60/1.79       ~ ((r1_tarski @ sk_B @ sk_C_2))),
% 1.60/1.79      inference('sup-', [status(thm)], ['14', '21'])).
% 1.60/1.79  thf('23', plain, (~ ((r1_tarski @ sk_B @ sk_C_2))),
% 1.60/1.79      inference('sat_resolution*', [status(thm)], ['2', '22'])).
% 1.60/1.79  thf('24', plain, (~ (r1_tarski @ sk_B @ sk_C_2)),
% 1.60/1.79      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 1.60/1.79  thf('25', plain,
% 1.60/1.79      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 1.60/1.79         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))))),
% 1.60/1.79      inference('split', [status(esa)], ['6'])).
% 1.60/1.79  thf('26', plain,
% 1.60/1.79      (((k3_subset_1 @ sk_A @ sk_C_2) = (k6_subset_1 @ sk_A @ sk_C_2))),
% 1.60/1.79      inference('sup-', [status(thm)], ['15', '18'])).
% 1.60/1.79  thf('27', plain,
% 1.60/1.79      (((r1_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_C_2)))
% 1.60/1.79         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))))),
% 1.60/1.79      inference('demod', [status(thm)], ['25', '26'])).
% 1.60/1.79  thf('28', plain,
% 1.60/1.79      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))) | 
% 1.60/1.79       ((r1_tarski @ sk_B @ sk_C_2))),
% 1.60/1.79      inference('split', [status(esa)], ['6'])).
% 1.60/1.79  thf('29', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 1.60/1.79      inference('sat_resolution*', [status(thm)], ['2', '22', '28'])).
% 1.60/1.79  thf('30', plain, ((r1_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_C_2))),
% 1.60/1.79      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 1.60/1.79  thf('31', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(d2_subset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( ( v1_xboole_0 @ A ) =>
% 1.60/1.79         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.60/1.79       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.60/1.79         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.60/1.79  thf('32', plain,
% 1.60/1.79      (![X34 : $i, X35 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X34 @ X35)
% 1.60/1.79          | (r2_hidden @ X34 @ X35)
% 1.60/1.79          | (v1_xboole_0 @ X35))),
% 1.60/1.79      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.60/1.79  thf('33', plain,
% 1.60/1.79      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.60/1.79        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['31', '32'])).
% 1.60/1.79  thf(fc1_subset_1, axiom,
% 1.60/1.79    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.60/1.79  thf('34', plain, (![X41 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X41))),
% 1.60/1.79      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.60/1.79  thf('35', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.60/1.79      inference('clc', [status(thm)], ['33', '34'])).
% 1.60/1.79  thf(d1_zfmisc_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.60/1.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.60/1.79  thf('36', plain,
% 1.60/1.79      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.60/1.79         (~ (r2_hidden @ X30 @ X29)
% 1.60/1.79          | (r1_tarski @ X30 @ X28)
% 1.60/1.79          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 1.60/1.79      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.60/1.79  thf('37', plain,
% 1.60/1.79      (![X28 : $i, X30 : $i]:
% 1.60/1.79         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 1.60/1.79      inference('simplify', [status(thm)], ['36'])).
% 1.60/1.79  thf('38', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 1.60/1.79      inference('sup-', [status(thm)], ['35', '37'])).
% 1.60/1.79  thf(t28_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.60/1.79  thf('39', plain,
% 1.60/1.79      (![X14 : $i, X15 : $i]:
% 1.60/1.79         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.60/1.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.60/1.79  thf('40', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 1.60/1.79      inference('sup-', [status(thm)], ['38', '39'])).
% 1.60/1.79  thf(commutativity_k3_xboole_0, axiom,
% 1.60/1.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.60/1.79  thf('41', plain,
% 1.60/1.79      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.60/1.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.60/1.79  thf(t100_xboole_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.60/1.79  thf('42', plain,
% 1.60/1.79      (![X10 : $i, X11 : $i]:
% 1.60/1.79         ((k4_xboole_0 @ X10 @ X11)
% 1.60/1.79           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.60/1.79  thf('43', plain,
% 1.60/1.79      (![X44 : $i, X45 : $i]:
% 1.60/1.79         ((k6_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))),
% 1.60/1.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.60/1.79  thf('44', plain,
% 1.60/1.79      (![X10 : $i, X11 : $i]:
% 1.60/1.79         ((k6_subset_1 @ X10 @ X11)
% 1.60/1.79           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.60/1.79      inference('demod', [status(thm)], ['42', '43'])).
% 1.60/1.79  thf('45', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i]:
% 1.60/1.79         ((k6_subset_1 @ X0 @ X1)
% 1.60/1.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.60/1.79      inference('sup+', [status(thm)], ['41', '44'])).
% 1.60/1.79  thf('46', plain,
% 1.60/1.79      (((k6_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.60/1.79      inference('sup+', [status(thm)], ['40', '45'])).
% 1.60/1.79  thf('47', plain, ((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.60/1.79      inference('demod', [status(thm)], ['30', '46'])).
% 1.60/1.79  thf('48', plain,
% 1.60/1.79      (((k6_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.60/1.79      inference('sup+', [status(thm)], ['40', '45'])).
% 1.60/1.79  thf(dt_k6_subset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.60/1.79  thf('49', plain,
% 1.60/1.79      (![X39 : $i, X40 : $i]:
% 1.60/1.79         (m1_subset_1 @ (k6_subset_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39))),
% 1.60/1.79      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.60/1.79  thf('50', plain,
% 1.60/1.79      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 1.60/1.79      inference('sup+', [status(thm)], ['48', '49'])).
% 1.60/1.79  thf(t43_subset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79       ( ![C:$i]:
% 1.60/1.79         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79           ( ( r1_xboole_0 @ B @ C ) <=>
% 1.60/1.79             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.60/1.79  thf('51', plain,
% 1.60/1.79      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 1.60/1.79          | ~ (r1_xboole_0 @ X48 @ X46)
% 1.60/1.79          | (r1_tarski @ X48 @ (k3_subset_1 @ X47 @ X46))
% 1.60/1.79          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t43_subset_1])).
% 1.60/1.79  thf('52', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.60/1.79          | (r1_tarski @ X0 @ 
% 1.60/1.79             (k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_2)))
% 1.60/1.79          | ~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_2)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['50', '51'])).
% 1.60/1.79  thf('53', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(involutiveness_k3_subset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.79       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.60/1.79  thf('54', plain,
% 1.60/1.79      (![X42 : $i, X43 : $i]:
% 1.60/1.79         (((k3_subset_1 @ X43 @ (k3_subset_1 @ X43 @ X42)) = (X42))
% 1.60/1.79          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 1.60/1.79      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.60/1.79  thf('55', plain,
% 1.60/1.79      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 1.60/1.79      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.79  thf('56', plain,
% 1.60/1.79      (((k3_subset_1 @ sk_A @ sk_C_2) = (k6_subset_1 @ sk_A @ sk_C_2))),
% 1.60/1.79      inference('sup-', [status(thm)], ['15', '18'])).
% 1.60/1.79  thf('57', plain,
% 1.60/1.79      (((k3_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 1.60/1.79      inference('demod', [status(thm)], ['55', '56'])).
% 1.60/1.79  thf('58', plain,
% 1.60/1.79      (((k6_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.60/1.79      inference('sup+', [status(thm)], ['40', '45'])).
% 1.60/1.79  thf('59', plain,
% 1.60/1.79      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 1.60/1.79      inference('demod', [status(thm)], ['57', '58'])).
% 1.60/1.79  thf('60', plain,
% 1.60/1.79      (![X0 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.60/1.79          | (r1_tarski @ X0 @ sk_C_2)
% 1.60/1.79          | ~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_2)))),
% 1.60/1.79      inference('demod', [status(thm)], ['52', '59'])).
% 1.60/1.79  thf('61', plain,
% 1.60/1.79      (((r1_tarski @ sk_B @ sk_C_2)
% 1.60/1.79        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['47', '60'])).
% 1.60/1.79  thf('62', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('63', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 1.60/1.79      inference('demod', [status(thm)], ['61', '62'])).
% 1.60/1.79  thf('64', plain, ($false), inference('demod', [status(thm)], ['24', '63'])).
% 1.60/1.79  
% 1.60/1.79  % SZS output end Refutation
% 1.60/1.79  
% 1.63/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
