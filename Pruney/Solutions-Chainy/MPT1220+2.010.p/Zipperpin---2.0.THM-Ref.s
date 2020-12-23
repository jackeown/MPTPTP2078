%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.swjmJyVrpq

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:40 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 290 expanded)
%              Number of leaves         :   36 ( 105 expanded)
%              Depth                    :   21
%              Number of atoms          :  571 (1737 expanded)
%              Number of equality atoms :   34 ( 107 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X19 ) @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_struct_0 @ X30 ) ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf(t27_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_tops_1])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('26',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('29',plain,(
    ! [X29: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','33'])).

thf('36',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','33'])).

thf('45',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ X31 @ ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('61',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.swjmJyVrpq
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:04:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 270 iterations in 0.131s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.41/0.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.41/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(fc3_struct_0, axiom,
% 0.41/0.60    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (![X29 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.41/0.60  thf(d3_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X1 : $i, X3 : $i]:
% 0.41/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf(dt_k2_subset_1, axiom,
% 0.41/0.60    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X19 : $i]: (m1_subset_1 @ (k2_subset_1 @ X19) @ (k1_zfmisc_1 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.41/0.60  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.41/0.60  thf('3', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.60  thf('4', plain, (![X19 : $i]: (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X19))),
% 0.41/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf(t5_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.41/0.60          ( v1_xboole_0 @ C ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X23 @ X24)
% 0.41/0.60          | ~ (v1_xboole_0 @ X25)
% 0.41/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t5_subset])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '6'])).
% 0.41/0.60  thf(t3_xboole_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X12 : $i]:
% 0.41/0.60         (((X12) = (k1_xboole_0)) | ~ (r1_tarski @ X12 @ k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X0) | ((k1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '9'])).
% 0.41/0.60  thf(t27_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_struct_0 @ A ) =>
% 0.41/0.60       ( ( k2_struct_0 @ A ) =
% 0.41/0.60         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X30 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X30)
% 0.41/0.60            = (k3_subset_1 @ (u1_struct_0 @ X30) @ (k1_struct_0 @ X30)))
% 0.41/0.60          | ~ (l1_struct_0 @ X30))),
% 0.41/0.60      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X0)
% 0.41/0.60            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X0)
% 0.41/0.60          | ((k2_struct_0 @ X0)
% 0.41/0.60              = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.41/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.60  thf('14', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.60  thf(t3_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X20 : $i, X22 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.60  thf(d5_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.41/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.60  thf(t3_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.41/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf(t83_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.41/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0) | ((k4_xboole_0 @ X1 @ X0) = (X1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 0.41/0.60          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['18', '23'])).
% 0.41/0.60  thf(t27_tops_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( l1_pre_topc @ A ) =>
% 0.41/0.60          ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t27_tops_1])).
% 0.41/0.60  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_l1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X28 : $i]: ((l1_struct_0 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.60  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X0) | ((k1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '9'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X29 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ k1_xboole_0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i]: (~ (l1_struct_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['30'])).
% 0.41/0.60  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['27', '31'])).
% 0.41/0.60  thf('33', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['24', '32'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['13', '33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['13', '33'])).
% 0.41/0.60  thf('36', plain, (![X19 : $i]: (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X19))),
% 0.41/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf(dt_k2_pre_topc, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60       ( m1_subset_1 @
% 0.41/0.60         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X26)
% 0.41/0.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.41/0.60          | (m1_subset_1 @ (k2_pre_topc @ X26 @ X27) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i]:
% 0.41/0.60         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.41/0.60             (u1_struct_0 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.41/0.60           (u1_struct_0 @ X0))
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['35', '40'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X28 : $i]: ((l1_struct_0 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.41/0.60             (u1_struct_0 @ X0)))),
% 0.41/0.60      inference('clc', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['13', '33'])).
% 0.41/0.60  thf('45', plain, (![X19 : $i]: (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X19))),
% 0.41/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf(t48_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X31 : $i, X32 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.41/0.60          | (r1_tarski @ X31 @ (k2_pre_topc @ X32 @ X31))
% 0.41/0.60          | ~ (l1_pre_topc @ X32))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.41/0.60             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.41/0.60           (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['44', '47'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X28 : $i]: ((l1_struct_0 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.41/0.60             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.41/0.60      inference('clc', [status(thm)], ['48', '49'])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X8 : $i, X10 : $i]:
% 0.41/0.60         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.41/0.60               (u1_struct_0 @ X0))
% 0.41/0.60          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '52'])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.60  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('58', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['34', '58'])).
% 0.41/0.60  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.60  thf('61', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['59', '60'])).
% 0.41/0.60  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
