%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NDO50QVS1B

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:08 EST 2020

% Result     : Theorem 3.18s
% Output     : Refutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 840 expanded)
%              Number of leaves         :   32 ( 280 expanded)
%              Depth                    :   19
%              Number of atoms          : 1162 (6113 expanded)
%              Number of equality atoms :   76 ( 460 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k4_xboole_0 @ X17 @ X16 ) @ ( k4_xboole_0 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( r1_tarski @ X33 @ X31 )
      | ( X32
       != ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ X33 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','41'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','70'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('85',plain,
    ( ( ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('87',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k4_xboole_0 @ X17 @ X16 ) @ ( k4_xboole_0 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('93',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('94',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('96',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('100',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ X33 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('102',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','104'])).

thf('106',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('111',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('113',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('115',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('117',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('119',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','94','119'])).

thf('121',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('123',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('124',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('126',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('127',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','127'])).

thf('129',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('130',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NDO50QVS1B
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 3.18/3.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.18/3.36  % Solved by: fo/fo7.sh
% 3.18/3.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.18/3.36  % done 6536 iterations in 2.892s
% 3.18/3.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.18/3.36  % SZS output start Refutation
% 3.18/3.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.18/3.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.18/3.36  thf(sk_B_type, type, sk_B: $i).
% 3.18/3.36  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.18/3.36  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.18/3.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.18/3.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.18/3.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.18/3.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.18/3.36  thf(sk_A_type, type, sk_A: $i).
% 3.18/3.36  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.18/3.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.18/3.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.18/3.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.18/3.36  thf(t31_subset_1, conjecture,
% 3.18/3.36    (![A:$i,B:$i]:
% 3.18/3.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.18/3.36       ( ![C:$i]:
% 3.18/3.36         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.18/3.36           ( ( r1_tarski @ B @ C ) <=>
% 3.18/3.36             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 3.18/3.36  thf(zf_stmt_0, negated_conjecture,
% 3.18/3.36    (~( ![A:$i,B:$i]:
% 3.18/3.36        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.18/3.36          ( ![C:$i]:
% 3.18/3.36            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.18/3.36              ( ( r1_tarski @ B @ C ) <=>
% 3.18/3.36                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 3.18/3.36    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 3.18/3.36  thf('0', plain,
% 3.18/3.36      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36           (k3_subset_1 @ sk_A @ sk_B))
% 3.18/3.36        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 3.18/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.18/3.36  thf('1', plain,
% 3.18/3.36      (~
% 3.18/3.36       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36         (k3_subset_1 @ sk_A @ sk_B))) | 
% 3.18/3.36       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 3.18/3.36      inference('split', [status(esa)], ['0'])).
% 3.18/3.36  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.18/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.18/3.36  thf(d5_subset_1, axiom,
% 3.18/3.36    (![A:$i,B:$i]:
% 3.18/3.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.18/3.36       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.18/3.36  thf('3', plain,
% 3.18/3.36      (![X38 : $i, X39 : $i]:
% 3.18/3.36         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 3.18/3.36          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 3.18/3.36      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.18/3.36  thf('4', plain,
% 3.18/3.36      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 3.18/3.36      inference('sup-', [status(thm)], ['2', '3'])).
% 3.18/3.36  thf('5', plain,
% 3.18/3.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36         (k3_subset_1 @ sk_A @ sk_B))
% 3.18/3.36        | (r1_tarski @ sk_B @ sk_C_1))),
% 3.18/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.18/3.36  thf('6', plain,
% 3.18/3.36      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 3.18/3.36      inference('split', [status(esa)], ['5'])).
% 3.18/3.36  thf(t34_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i,C:$i]:
% 3.18/3.36     ( ( r1_tarski @ A @ B ) =>
% 3.18/3.36       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 3.18/3.36  thf('7', plain,
% 3.18/3.36      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.18/3.36         (~ (r1_tarski @ X15 @ X16)
% 3.18/3.36          | (r1_tarski @ (k4_xboole_0 @ X17 @ X16) @ (k4_xboole_0 @ X17 @ X15)))),
% 3.18/3.36      inference('cnf', [status(esa)], [t34_xboole_1])).
% 3.18/3.36  thf('8', plain,
% 3.18/3.36      ((![X0 : $i]:
% 3.18/3.36          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 3.18/3.36         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['6', '7'])).
% 3.18/3.36  thf('9', plain,
% 3.18/3.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 3.18/3.36      inference('sup+', [status(thm)], ['4', '8'])).
% 3.18/3.36  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.18/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.18/3.36  thf('11', plain,
% 3.18/3.36      (![X38 : $i, X39 : $i]:
% 3.18/3.36         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 3.18/3.36          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 3.18/3.36      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.18/3.36  thf('12', plain,
% 3.18/3.36      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.18/3.36      inference('sup-', [status(thm)], ['10', '11'])).
% 3.18/3.36  thf('13', plain,
% 3.18/3.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 3.18/3.36      inference('demod', [status(thm)], ['9', '12'])).
% 3.18/3.36  thf('14', plain,
% 3.18/3.36      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36           (k3_subset_1 @ sk_A @ sk_B)))
% 3.18/3.36         <= (~
% 3.18/3.36             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.18/3.36      inference('split', [status(esa)], ['0'])).
% 3.18/3.36  thf('15', plain,
% 3.18/3.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36         (k3_subset_1 @ sk_A @ sk_B))) | 
% 3.18/3.36       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 3.18/3.36      inference('sup-', [status(thm)], ['13', '14'])).
% 3.18/3.36  thf('16', plain,
% 3.18/3.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36         (k3_subset_1 @ sk_A @ sk_B))) | 
% 3.18/3.36       ((r1_tarski @ sk_B @ sk_C_1))),
% 3.18/3.36      inference('split', [status(esa)], ['5'])).
% 3.18/3.36  thf(t7_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.18/3.36  thf('17', plain,
% 3.18/3.36      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 3.18/3.36      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.18/3.36  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.18/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.18/3.36  thf(d2_subset_1, axiom,
% 3.18/3.36    (![A:$i,B:$i]:
% 3.18/3.36     ( ( ( v1_xboole_0 @ A ) =>
% 3.18/3.36         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.18/3.36       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.18/3.36         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.18/3.36  thf('19', plain,
% 3.18/3.36      (![X35 : $i, X36 : $i]:
% 3.18/3.36         (~ (m1_subset_1 @ X35 @ X36)
% 3.18/3.36          | (r2_hidden @ X35 @ X36)
% 3.18/3.36          | (v1_xboole_0 @ X36))),
% 3.18/3.36      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.18/3.36  thf('20', plain,
% 3.18/3.36      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.18/3.36        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['18', '19'])).
% 3.18/3.36  thf(fc1_subset_1, axiom,
% 3.18/3.36    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.18/3.36  thf('21', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 3.18/3.36      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.18/3.36  thf('22', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.18/3.36      inference('clc', [status(thm)], ['20', '21'])).
% 3.18/3.36  thf(d1_zfmisc_1, axiom,
% 3.18/3.36    (![A:$i,B:$i]:
% 3.18/3.36     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 3.18/3.36       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 3.18/3.36  thf('23', plain,
% 3.18/3.36      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.18/3.36         (~ (r2_hidden @ X33 @ X32)
% 3.18/3.36          | (r1_tarski @ X33 @ X31)
% 3.18/3.36          | ((X32) != (k1_zfmisc_1 @ X31)))),
% 3.18/3.36      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 3.18/3.36  thf('24', plain,
% 3.18/3.36      (![X31 : $i, X33 : $i]:
% 3.18/3.36         ((r1_tarski @ X33 @ X31) | ~ (r2_hidden @ X33 @ (k1_zfmisc_1 @ X31)))),
% 3.18/3.36      inference('simplify', [status(thm)], ['23'])).
% 3.18/3.36  thf('25', plain, ((r1_tarski @ sk_B @ sk_A)),
% 3.18/3.36      inference('sup-', [status(thm)], ['22', '24'])).
% 3.18/3.36  thf(t1_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i,C:$i]:
% 3.18/3.36     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 3.18/3.36       ( r1_tarski @ A @ C ) ))).
% 3.18/3.36  thf('26', plain,
% 3.18/3.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.18/3.36         (~ (r1_tarski @ X11 @ X12)
% 3.18/3.36          | ~ (r1_tarski @ X12 @ X13)
% 3.18/3.36          | (r1_tarski @ X11 @ X13))),
% 3.18/3.36      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.18/3.36  thf('27', plain,
% 3.18/3.36      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['25', '26'])).
% 3.18/3.36  thf('28', plain,
% 3.18/3.36      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ X0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['17', '27'])).
% 3.18/3.36  thf(t43_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i,C:$i]:
% 3.18/3.36     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.18/3.36       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.18/3.36  thf('29', plain,
% 3.18/3.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.18/3.36         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.18/3.36          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.18/3.36      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.18/3.36  thf('30', plain,
% 3.18/3.36      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ X0)),
% 3.18/3.36      inference('sup-', [status(thm)], ['28', '29'])).
% 3.18/3.36  thf(t100_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i]:
% 3.18/3.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.18/3.36  thf('31', plain,
% 3.18/3.36      (![X7 : $i, X8 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X7 @ X8)
% 3.18/3.36           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 3.18/3.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.18/3.36  thf('32', plain,
% 3.18/3.36      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 3.18/3.36      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.18/3.36  thf('33', plain,
% 3.18/3.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.18/3.36         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.18/3.36          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.18/3.36      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.18/3.36  thf('34', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 3.18/3.36      inference('sup-', [status(thm)], ['32', '33'])).
% 3.18/3.36  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.18/3.36  thf('35', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 3.18/3.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.18/3.36  thf(d10_xboole_0, axiom,
% 3.18/3.36    (![A:$i,B:$i]:
% 3.18/3.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.18/3.36  thf('36', plain,
% 3.18/3.36      (![X4 : $i, X6 : $i]:
% 3.18/3.36         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.18/3.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.18/3.36  thf('37', plain,
% 3.18/3.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['35', '36'])).
% 3.18/3.36  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['34', '37'])).
% 3.18/3.36  thf('39', plain,
% 3.18/3.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['35', '36'])).
% 3.18/3.36  thf('40', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]:
% 3.18/3.36         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['38', '39'])).
% 3.18/3.36  thf('41', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]:
% 3.18/3.36         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))
% 3.18/3.36          | ((X1) = (k1_xboole_0)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['31', '40'])).
% 3.18/3.36  thf('42', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['30', '41'])).
% 3.18/3.36  thf(t48_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i]:
% 3.18/3.36     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.18/3.36  thf('43', plain,
% 3.18/3.36      (![X26 : $i, X27 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 3.18/3.36           = (k3_xboole_0 @ X26 @ X27))),
% 3.18/3.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.18/3.36  thf('44', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.18/3.36      inference('sup+', [status(thm)], ['42', '43'])).
% 3.18/3.36  thf('45', plain,
% 3.18/3.36      (![X26 : $i, X27 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 3.18/3.36           = (k3_xboole_0 @ X26 @ X27))),
% 3.18/3.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.18/3.36  thf(t36_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.18/3.36  thf('46', plain,
% 3.18/3.36      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 3.18/3.36      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.18/3.36  thf('47', plain,
% 3.18/3.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['35', '36'])).
% 3.18/3.36  thf('48', plain,
% 3.18/3.36      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['46', '47'])).
% 3.18/3.36  thf('49', plain,
% 3.18/3.36      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.18/3.36      inference('sup+', [status(thm)], ['45', '48'])).
% 3.18/3.36  thf(commutativity_k3_xboole_0, axiom,
% 3.18/3.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.18/3.36  thf('50', plain,
% 3.18/3.36      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.18/3.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.18/3.36  thf('51', plain,
% 3.18/3.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.18/3.36      inference('sup+', [status(thm)], ['49', '50'])).
% 3.18/3.36  thf('52', plain,
% 3.18/3.36      (![X7 : $i, X8 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X7 @ X8)
% 3.18/3.36           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 3.18/3.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.18/3.36  thf('53', plain,
% 3.18/3.36      (![X0 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.18/3.36      inference('sup+', [status(thm)], ['51', '52'])).
% 3.18/3.36  thf('54', plain,
% 3.18/3.36      (((k5_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.18/3.36      inference('demod', [status(thm)], ['44', '53'])).
% 3.18/3.36  thf('55', plain,
% 3.18/3.36      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 3.18/3.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.18/3.36  thf('56', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 3.18/3.36      inference('simplify', [status(thm)], ['55'])).
% 3.18/3.36  thf('57', plain,
% 3.18/3.36      (![X0 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.18/3.36      inference('sup+', [status(thm)], ['51', '52'])).
% 3.18/3.36  thf(t44_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i,C:$i]:
% 3.18/3.36     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.18/3.36       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.18/3.36  thf('58', plain,
% 3.18/3.36      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.18/3.36         ((r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 3.18/3.36          | ~ (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25))),
% 3.18/3.36      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.18/3.36  thf('59', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]:
% 3.18/3.36         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 3.18/3.36          | (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['57', '58'])).
% 3.18/3.36  thf('60', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 3.18/3.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.18/3.36  thf(t12_xboole_1, axiom,
% 3.18/3.36    (![A:$i,B:$i]:
% 3.18/3.36     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.18/3.36  thf('61', plain,
% 3.18/3.36      (![X9 : $i, X10 : $i]:
% 3.18/3.36         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 3.18/3.36      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.18/3.36  thf('62', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['60', '61'])).
% 3.18/3.36  thf('63', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]:
% 3.18/3.36         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 3.18/3.36          | (r1_tarski @ X0 @ X1))),
% 3.18/3.36      inference('demod', [status(thm)], ['59', '62'])).
% 3.18/3.36  thf('64', plain,
% 3.18/3.36      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['56', '63'])).
% 3.18/3.36  thf('65', plain,
% 3.18/3.36      (![X4 : $i, X6 : $i]:
% 3.18/3.36         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.18/3.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.18/3.36  thf('66', plain,
% 3.18/3.36      (![X0 : $i]:
% 3.18/3.36         (~ (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 3.18/3.36          | ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['64', '65'])).
% 3.18/3.36  thf('67', plain,
% 3.18/3.36      (![X0 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.18/3.36      inference('sup+', [status(thm)], ['51', '52'])).
% 3.18/3.36  thf('68', plain,
% 3.18/3.36      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 3.18/3.36      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.18/3.36  thf('69', plain,
% 3.18/3.36      (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 3.18/3.36      inference('sup+', [status(thm)], ['67', '68'])).
% 3.18/3.36  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.18/3.36      inference('demod', [status(thm)], ['66', '69'])).
% 3.18/3.36  thf('71', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.18/3.36      inference('demod', [status(thm)], ['54', '70'])).
% 3.18/3.36  thf('72', plain,
% 3.18/3.36      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.18/3.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.18/3.36  thf('73', plain,
% 3.18/3.36      (![X7 : $i, X8 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X7 @ X8)
% 3.18/3.36           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 3.18/3.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.18/3.36  thf('74', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X0 @ X1)
% 3.18/3.36           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.18/3.36      inference('sup+', [status(thm)], ['72', '73'])).
% 3.18/3.36  thf('75', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.18/3.36      inference('sup+', [status(thm)], ['71', '74'])).
% 3.18/3.36  thf('76', plain,
% 3.18/3.36      (![X26 : $i, X27 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 3.18/3.36           = (k3_xboole_0 @ X26 @ X27))),
% 3.18/3.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.18/3.36  thf('77', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 3.18/3.36         = (k3_xboole_0 @ sk_A @ sk_B))),
% 3.18/3.36      inference('sup+', [status(thm)], ['75', '76'])).
% 3.18/3.36  thf('78', plain,
% 3.18/3.36      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.18/3.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.18/3.36  thf('79', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.18/3.36      inference('demod', [status(thm)], ['54', '70'])).
% 3.18/3.36  thf('80', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 3.18/3.36      inference('demod', [status(thm)], ['77', '78', '79'])).
% 3.18/3.36  thf('81', plain,
% 3.18/3.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36         (k3_subset_1 @ sk_A @ sk_B)))
% 3.18/3.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.18/3.36      inference('split', [status(esa)], ['5'])).
% 3.18/3.36  thf('82', plain,
% 3.18/3.36      (![X9 : $i, X10 : $i]:
% 3.18/3.36         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 3.18/3.36      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.18/3.36  thf('83', plain,
% 3.18/3.36      ((((k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36          (k3_subset_1 @ sk_A @ sk_B)) = (k3_subset_1 @ sk_A @ sk_B)))
% 3.18/3.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.18/3.36      inference('sup-', [status(thm)], ['81', '82'])).
% 3.18/3.36  thf(commutativity_k2_xboole_0, axiom,
% 3.18/3.36    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.18/3.36  thf('84', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.18/3.36      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.18/3.36  thf('85', plain,
% 3.18/3.36      ((((k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 3.18/3.36          (k3_subset_1 @ sk_A @ sk_C_1)) = (k3_subset_1 @ sk_A @ sk_B)))
% 3.18/3.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.18/3.36      inference('demod', [status(thm)], ['83', '84'])).
% 3.18/3.36  thf('86', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.18/3.36      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.18/3.36  thf('87', plain,
% 3.18/3.36      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 3.18/3.36      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.18/3.36  thf('88', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.18/3.36      inference('sup+', [status(thm)], ['86', '87'])).
% 3.18/3.36  thf('89', plain,
% 3.18/3.36      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.18/3.36         (~ (r1_tarski @ X15 @ X16)
% 3.18/3.36          | (r1_tarski @ (k4_xboole_0 @ X17 @ X16) @ (k4_xboole_0 @ X17 @ X15)))),
% 3.18/3.36      inference('cnf', [status(esa)], [t34_xboole_1])).
% 3.18/3.36  thf('90', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.18/3.36         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 3.18/3.36          (k4_xboole_0 @ X2 @ X0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['88', '89'])).
% 3.18/3.36  thf('91', plain,
% 3.18/3.36      ((![X0 : $i]:
% 3.18/3.36          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 3.18/3.36           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 3.18/3.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.18/3.36      inference('sup+', [status(thm)], ['85', '90'])).
% 3.18/3.36  thf('92', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.18/3.36      inference('sup+', [status(thm)], ['71', '74'])).
% 3.18/3.36  thf('93', plain,
% 3.18/3.36      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.18/3.36      inference('sup-', [status(thm)], ['10', '11'])).
% 3.18/3.36  thf('94', plain,
% 3.18/3.36      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 3.18/3.36      inference('sup+', [status(thm)], ['92', '93'])).
% 3.18/3.36  thf('95', plain,
% 3.18/3.36      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 3.18/3.36      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.18/3.36  thf('96', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.18/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.18/3.36  thf('97', plain,
% 3.18/3.36      (![X35 : $i, X36 : $i]:
% 3.18/3.36         (~ (m1_subset_1 @ X35 @ X36)
% 3.18/3.36          | (r2_hidden @ X35 @ X36)
% 3.18/3.36          | (v1_xboole_0 @ X36))),
% 3.18/3.36      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.18/3.36  thf('98', plain,
% 3.18/3.36      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.18/3.36        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['96', '97'])).
% 3.18/3.36  thf('99', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 3.18/3.36      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.18/3.36  thf('100', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.18/3.36      inference('clc', [status(thm)], ['98', '99'])).
% 3.18/3.36  thf('101', plain,
% 3.18/3.36      (![X31 : $i, X33 : $i]:
% 3.18/3.36         ((r1_tarski @ X33 @ X31) | ~ (r2_hidden @ X33 @ (k1_zfmisc_1 @ X31)))),
% 3.18/3.36      inference('simplify', [status(thm)], ['23'])).
% 3.18/3.36  thf('102', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 3.18/3.36      inference('sup-', [status(thm)], ['100', '101'])).
% 3.18/3.36  thf('103', plain,
% 3.18/3.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.18/3.36         (~ (r1_tarski @ X11 @ X12)
% 3.18/3.36          | ~ (r1_tarski @ X12 @ X13)
% 3.18/3.36          | (r1_tarski @ X11 @ X13))),
% 3.18/3.36      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.18/3.36  thf('104', plain,
% 3.18/3.36      (![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['102', '103'])).
% 3.18/3.36  thf('105', plain,
% 3.18/3.36      (![X0 : $i]: (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['95', '104'])).
% 3.18/3.36  thf('106', plain,
% 3.18/3.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.18/3.36         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 3.18/3.36          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 3.18/3.36      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.18/3.36  thf('107', plain,
% 3.18/3.36      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_A) @ X0)),
% 3.18/3.36      inference('sup-', [status(thm)], ['105', '106'])).
% 3.18/3.36  thf('108', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]:
% 3.18/3.36         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))
% 3.18/3.36          | ((X1) = (k1_xboole_0)))),
% 3.18/3.36      inference('sup-', [status(thm)], ['31', '40'])).
% 3.18/3.36  thf('109', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 3.18/3.36      inference('sup-', [status(thm)], ['107', '108'])).
% 3.18/3.36  thf('110', plain,
% 3.18/3.36      (![X26 : $i, X27 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 3.18/3.36           = (k3_xboole_0 @ X26 @ X27))),
% 3.18/3.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.18/3.36  thf('111', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 3.18/3.36      inference('sup+', [status(thm)], ['109', '110'])).
% 3.18/3.36  thf('112', plain,
% 3.18/3.36      (![X0 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.18/3.36      inference('sup+', [status(thm)], ['51', '52'])).
% 3.18/3.36  thf('113', plain,
% 3.18/3.36      (((k5_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 3.18/3.36      inference('demod', [status(thm)], ['111', '112'])).
% 3.18/3.36  thf('114', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.18/3.36      inference('demod', [status(thm)], ['66', '69'])).
% 3.18/3.36  thf('115', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 3.18/3.36      inference('demod', [status(thm)], ['113', '114'])).
% 3.18/3.36  thf('116', plain,
% 3.18/3.36      (![X0 : $i, X1 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X0 @ X1)
% 3.18/3.36           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.18/3.36      inference('sup+', [status(thm)], ['72', '73'])).
% 3.18/3.36  thf('117', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 3.18/3.36      inference('sup+', [status(thm)], ['115', '116'])).
% 3.18/3.36  thf('118', plain,
% 3.18/3.36      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 3.18/3.36      inference('sup-', [status(thm)], ['2', '3'])).
% 3.18/3.36  thf('119', plain,
% 3.18/3.36      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 3.18/3.36      inference('sup+', [status(thm)], ['117', '118'])).
% 3.18/3.36  thf('120', plain,
% 3.18/3.36      ((![X0 : $i]:
% 3.18/3.36          (r1_tarski @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B)) @ 
% 3.18/3.36           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))))
% 3.18/3.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.18/3.36      inference('demod', [status(thm)], ['91', '94', '119'])).
% 3.18/3.36  thf('121', plain,
% 3.18/3.36      (((r1_tarski @ sk_B @ 
% 3.18/3.36         (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))))
% 3.18/3.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.18/3.36      inference('sup+', [status(thm)], ['80', '120'])).
% 3.18/3.36  thf('122', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 3.18/3.36      inference('sup+', [status(thm)], ['115', '116'])).
% 3.18/3.36  thf('123', plain,
% 3.18/3.36      (![X26 : $i, X27 : $i]:
% 3.18/3.36         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 3.18/3.36           = (k3_xboole_0 @ X26 @ X27))),
% 3.18/3.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.18/3.36  thf('124', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 3.18/3.36         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 3.18/3.36      inference('sup+', [status(thm)], ['122', '123'])).
% 3.18/3.36  thf('125', plain,
% 3.18/3.36      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.18/3.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.18/3.36  thf('126', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 3.18/3.36      inference('demod', [status(thm)], ['113', '114'])).
% 3.18/3.36  thf('127', plain,
% 3.18/3.36      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 3.18/3.36      inference('demod', [status(thm)], ['124', '125', '126'])).
% 3.18/3.36  thf('128', plain,
% 3.18/3.36      (((r1_tarski @ sk_B @ sk_C_1))
% 3.18/3.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.18/3.36      inference('demod', [status(thm)], ['121', '127'])).
% 3.18/3.36  thf('129', plain,
% 3.18/3.36      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 3.18/3.36      inference('split', [status(esa)], ['0'])).
% 3.18/3.36  thf('130', plain,
% 3.18/3.36      (~
% 3.18/3.36       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.18/3.36         (k3_subset_1 @ sk_A @ sk_B))) | 
% 3.18/3.36       ((r1_tarski @ sk_B @ sk_C_1))),
% 3.18/3.36      inference('sup-', [status(thm)], ['128', '129'])).
% 3.18/3.36  thf('131', plain, ($false),
% 3.18/3.36      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '130'])).
% 3.18/3.36  
% 3.18/3.36  % SZS output end Refutation
% 3.18/3.36  
% 3.18/3.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
