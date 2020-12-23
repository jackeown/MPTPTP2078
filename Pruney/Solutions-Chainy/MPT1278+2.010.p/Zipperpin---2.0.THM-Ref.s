%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qlujTCbz14

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:40 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 458 expanded)
%              Number of leaves         :   36 ( 153 expanded)
%              Depth                    :   19
%              Number of atoms          :  951 (4856 expanded)
%              Number of equality atoms :   52 ( 244 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X21 ) @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( r1_tarski @ X43 @ ( k2_pre_topc @ X44 @ X43 ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t97_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v3_tops_1 @ B @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_tops_1])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v1_tops_1 @ X47 @ X48 )
      | ( ( k2_pre_topc @ X48 @ X47 )
        = ( k2_struct_0 @ X48 ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v4_pre_topc @ X45 @ X46 )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = X45 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('32',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 ) @ X50 )
      | ( v4_pre_topc @ X49 @ X50 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X25 @ ( k3_subset_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('37',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['33','34','37','38'])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('42',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 ) @ X55 )
      | ~ ( v3_tops_1 @ X54 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','40','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','47'])).

thf(t79_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v1_tops_1 @ X51 @ X52 )
      | ~ ( r1_tarski @ X51 @ X53 )
      | ( v1_tops_1 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ X0 )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('53',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','40','46'])).

thf('54',plain,(
    v1_tops_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','55'])).

thf('57',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('58',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','40','46'])).

thf('59',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('62',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v1_tops_1 @ X47 @ X48 )
      | ( ( k2_pre_topc @ X48 @ X47 )
        = ( k2_struct_0 @ X48 ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['12','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('71',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t64_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( ( k3_subset_1 @ A @ B )
              = ( k3_subset_1 @ A @ C ) )
           => ( B = C ) ) ) ) )).

thf('72',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( X32 = X30 )
      | ( ( k3_subset_1 @ X31 @ X32 )
       != ( k3_subset_1 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t64_subset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X1 )
       != ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('75',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('77',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X1 )
       != X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
 != ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','40','46'])).

thf('84',plain,(
    ( k2_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qlujTCbz14
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:43:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.87/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.87/1.06  % Solved by: fo/fo7.sh
% 0.87/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.06  % done 1216 iterations in 0.623s
% 0.87/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.87/1.06  % SZS output start Refutation
% 0.87/1.06  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.87/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.87/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.87/1.06  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.87/1.06  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.87/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.87/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.06  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.87/1.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.87/1.06  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.87/1.06  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.87/1.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.87/1.06  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.87/1.06  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.87/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.87/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.87/1.06  thf(dt_k2_subset_1, axiom,
% 0.87/1.06    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.87/1.06  thf('0', plain,
% 0.87/1.06      (![X21 : $i]: (m1_subset_1 @ (k2_subset_1 @ X21) @ (k1_zfmisc_1 @ X21))),
% 0.87/1.06      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.87/1.06  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.87/1.06  thf('1', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.87/1.06      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.87/1.06  thf('2', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.87/1.06      inference('demod', [status(thm)], ['0', '1'])).
% 0.87/1.06  thf(t48_pre_topc, axiom,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ( l1_pre_topc @ A ) =>
% 0.87/1.06       ( ![B:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.87/1.06  thf('3', plain,
% 0.87/1.06      (![X43 : $i, X44 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.87/1.06          | (r1_tarski @ X43 @ (k2_pre_topc @ X44 @ X43))
% 0.87/1.06          | ~ (l1_pre_topc @ X44))),
% 0.87/1.06      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.87/1.06  thf('4', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (l1_pre_topc @ X0)
% 0.87/1.06          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.87/1.06             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.87/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.87/1.06  thf(d10_xboole_0, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.87/1.06  thf('5', plain,
% 0.87/1.06      (![X8 : $i, X10 : $i]:
% 0.87/1.06         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.87/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.06  thf('6', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (l1_pre_topc @ X0)
% 0.87/1.06          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.87/1.06               (u1_struct_0 @ X0))
% 0.87/1.06          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['4', '5'])).
% 0.87/1.06  thf('7', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.87/1.06      inference('demod', [status(thm)], ['0', '1'])).
% 0.87/1.06  thf(dt_k2_pre_topc, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( ( l1_pre_topc @ A ) & 
% 0.87/1.06         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.87/1.06       ( m1_subset_1 @
% 0.87/1.06         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.87/1.06  thf('8', plain,
% 0.87/1.06      (![X41 : $i, X42 : $i]:
% 0.87/1.06         (~ (l1_pre_topc @ X41)
% 0.87/1.06          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.87/1.06          | (m1_subset_1 @ (k2_pre_topc @ X41 @ X42) @ 
% 0.87/1.06             (k1_zfmisc_1 @ (u1_struct_0 @ X41))))),
% 0.87/1.06      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.87/1.06  thf('9', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.87/1.06           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.87/1.06          | ~ (l1_pre_topc @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['7', '8'])).
% 0.87/1.06  thf(t3_subset, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.87/1.06  thf('10', plain,
% 0.87/1.06      (![X33 : $i, X34 : $i]:
% 0.87/1.06         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.06  thf('11', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (l1_pre_topc @ X0)
% 0.87/1.06          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.87/1.06             (u1_struct_0 @ X0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['9', '10'])).
% 0.87/1.06  thf('12', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.87/1.06          | ~ (l1_pre_topc @ X0))),
% 0.87/1.06      inference('clc', [status(thm)], ['6', '11'])).
% 0.87/1.06  thf('13', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.87/1.06      inference('demod', [status(thm)], ['0', '1'])).
% 0.87/1.06  thf(t97_tops_1, conjecture,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.87/1.06       ( ![B:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.87/1.06             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.87/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.06    (~( ![A:$i]:
% 0.87/1.06        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.87/1.06          ( ![B:$i]:
% 0.87/1.06            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.87/1.06                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.87/1.06    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.87/1.06  thf('14', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf(d5_subset_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.06       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.87/1.06  thf('15', plain,
% 0.87/1.06      (![X19 : $i, X20 : $i]:
% 0.87/1.06         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.87/1.06          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.87/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.87/1.06  thf('16', plain,
% 0.87/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.87/1.06         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.87/1.06      inference('sup-', [status(thm)], ['14', '15'])).
% 0.87/1.06  thf(t36_xboole_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.87/1.06  thf('17', plain,
% 0.87/1.06      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.87/1.06      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.87/1.06  thf('18', plain,
% 0.87/1.06      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.87/1.06        (u1_struct_0 @ sk_A))),
% 0.87/1.06      inference('sup+', [status(thm)], ['16', '17'])).
% 0.87/1.06  thf('19', plain,
% 0.87/1.06      (![X33 : $i, X35 : $i]:
% 0.87/1.06         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 0.87/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.06  thf('20', plain,
% 0.87/1.06      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.87/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.87/1.06  thf('21', plain,
% 0.87/1.06      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.87/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.87/1.06  thf(d3_tops_1, axiom,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ( l1_pre_topc @ A ) =>
% 0.87/1.06       ( ![B:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06           ( ( v1_tops_1 @ B @ A ) <=>
% 0.87/1.06             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.87/1.06  thf('22', plain,
% 0.87/1.06      (![X47 : $i, X48 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.87/1.06          | ~ (v1_tops_1 @ X47 @ X48)
% 0.87/1.06          | ((k2_pre_topc @ X48 @ X47) = (k2_struct_0 @ X48))
% 0.87/1.06          | ~ (l1_pre_topc @ X48))),
% 0.87/1.06      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.87/1.06  thf('23', plain,
% 0.87/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.87/1.06        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.87/1.06            = (k2_struct_0 @ sk_A))
% 0.87/1.06        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['21', '22'])).
% 0.87/1.06  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('25', plain,
% 0.87/1.06      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.87/1.06          = (k2_struct_0 @ sk_A))
% 0.87/1.06        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['23', '24'])).
% 0.87/1.06  thf('26', plain,
% 0.87/1.06      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.87/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.87/1.06  thf(t52_pre_topc, axiom,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ( l1_pre_topc @ A ) =>
% 0.87/1.06       ( ![B:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.87/1.06             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.87/1.06               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.87/1.06  thf('27', plain,
% 0.87/1.06      (![X45 : $i, X46 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.87/1.06          | ~ (v4_pre_topc @ X45 @ X46)
% 0.87/1.06          | ((k2_pre_topc @ X46 @ X45) = (X45))
% 0.87/1.06          | ~ (l1_pre_topc @ X46))),
% 0.87/1.06      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.87/1.06  thf('28', plain,
% 0.87/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.87/1.06        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.87/1.06            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.87/1.06        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['26', '27'])).
% 0.87/1.06  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('30', plain,
% 0.87/1.06      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.87/1.06          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.87/1.06        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['28', '29'])).
% 0.87/1.06  thf('31', plain,
% 0.87/1.06      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.87/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.87/1.06  thf(t29_tops_1, axiom,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ( l1_pre_topc @ A ) =>
% 0.87/1.06       ( ![B:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06           ( ( v4_pre_topc @ B @ A ) <=>
% 0.87/1.06             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.87/1.06  thf('32', plain,
% 0.87/1.06      (![X49 : $i, X50 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.87/1.06          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X50) @ X49) @ X50)
% 0.87/1.06          | (v4_pre_topc @ X49 @ X50)
% 0.87/1.06          | ~ (l1_pre_topc @ X50))),
% 0.87/1.06      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.87/1.06  thf('33', plain,
% 0.87/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.87/1.06        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.87/1.06        | ~ (v3_pre_topc @ 
% 0.87/1.06             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.87/1.06              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.87/1.06             sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['31', '32'])).
% 0.87/1.06  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('35', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf(involutiveness_k3_subset_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.06       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.87/1.06  thf('36', plain,
% 0.87/1.06      (![X24 : $i, X25 : $i]:
% 0.87/1.06         (((k3_subset_1 @ X25 @ (k3_subset_1 @ X25 @ X24)) = (X24))
% 0.87/1.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.87/1.06      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.87/1.06  thf('37', plain,
% 0.87/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.87/1.06         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.87/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.87/1.06  thf('38', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('39', plain,
% 0.87/1.06      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.87/1.06      inference('demod', [status(thm)], ['33', '34', '37', '38'])).
% 0.87/1.06  thf('40', plain,
% 0.87/1.06      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.87/1.06         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.87/1.06      inference('demod', [status(thm)], ['30', '39'])).
% 0.87/1.06  thf('41', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf(t91_tops_1, axiom,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ( l1_pre_topc @ A ) =>
% 0.87/1.06       ( ![B:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06           ( ( v3_tops_1 @ B @ A ) =>
% 0.87/1.06             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.87/1.06  thf('42', plain,
% 0.87/1.06      (![X54 : $i, X55 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 0.87/1.06          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X55) @ X54) @ X55)
% 0.87/1.06          | ~ (v3_tops_1 @ X54 @ X55)
% 0.87/1.06          | ~ (l1_pre_topc @ X55))),
% 0.87/1.06      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.87/1.06  thf('43', plain,
% 0.87/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.87/1.06        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.87/1.06        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['41', '42'])).
% 0.87/1.06  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('45', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('46', plain,
% 0.87/1.06      ((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.87/1.06      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.87/1.06  thf('47', plain,
% 0.87/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['25', '40', '46'])).
% 0.87/1.06  thf('48', plain,
% 0.87/1.06      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.87/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('demod', [status(thm)], ['20', '47'])).
% 0.87/1.06  thf(t79_tops_1, axiom,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ( l1_pre_topc @ A ) =>
% 0.87/1.06       ( ![B:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06           ( ![C:$i]:
% 0.87/1.06             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.06               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.87/1.06                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.87/1.06  thf('49', plain,
% 0.87/1.06      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.87/1.06          | ~ (v1_tops_1 @ X51 @ X52)
% 0.87/1.06          | ~ (r1_tarski @ X51 @ X53)
% 0.87/1.06          | (v1_tops_1 @ X53 @ X52)
% 0.87/1.06          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.87/1.06          | ~ (l1_pre_topc @ X52))),
% 0.87/1.06      inference('cnf', [status(esa)], [t79_tops_1])).
% 0.87/1.06  thf('50', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (l1_pre_topc @ sk_A)
% 0.87/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.87/1.06          | (v1_tops_1 @ X0 @ sk_A)
% 0.87/1.06          | ~ (r1_tarski @ (k2_struct_0 @ sk_A) @ X0)
% 0.87/1.06          | ~ (v1_tops_1 @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['48', '49'])).
% 0.87/1.06  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('52', plain,
% 0.87/1.06      ((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.87/1.06      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.87/1.06  thf('53', plain,
% 0.87/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['25', '40', '46'])).
% 0.87/1.06  thf('54', plain, ((v1_tops_1 @ (k2_struct_0 @ sk_A) @ sk_A)),
% 0.87/1.06      inference('demod', [status(thm)], ['52', '53'])).
% 0.87/1.06  thf('55', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.87/1.06          | (v1_tops_1 @ X0 @ sk_A)
% 0.87/1.06          | ~ (r1_tarski @ (k2_struct_0 @ sk_A) @ X0))),
% 0.87/1.06      inference('demod', [status(thm)], ['50', '51', '54'])).
% 0.87/1.06  thf('56', plain,
% 0.87/1.06      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.87/1.06        | (v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['13', '55'])).
% 0.87/1.06  thf('57', plain,
% 0.87/1.06      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.87/1.06        (u1_struct_0 @ sk_A))),
% 0.87/1.06      inference('sup+', [status(thm)], ['16', '17'])).
% 0.87/1.06  thf('58', plain,
% 0.87/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['25', '40', '46'])).
% 0.87/1.06  thf('59', plain, ((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['57', '58'])).
% 0.87/1.06  thf('60', plain, ((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.87/1.06      inference('demod', [status(thm)], ['56', '59'])).
% 0.87/1.06  thf('61', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.87/1.06      inference('demod', [status(thm)], ['0', '1'])).
% 0.87/1.06  thf('62', plain,
% 0.87/1.06      (![X47 : $i, X48 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.87/1.06          | ~ (v1_tops_1 @ X47 @ X48)
% 0.87/1.06          | ((k2_pre_topc @ X48 @ X47) = (k2_struct_0 @ X48))
% 0.87/1.06          | ~ (l1_pre_topc @ X48))),
% 0.87/1.06      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.87/1.06  thf('63', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (l1_pre_topc @ X0)
% 0.87/1.06          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.87/1.06          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['61', '62'])).
% 0.87/1.06  thf('64', plain,
% 0.87/1.06      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.87/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['60', '63'])).
% 0.87/1.06  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('66', plain,
% 0.87/1.06      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['64', '65'])).
% 0.87/1.06  thf('67', plain,
% 0.87/1.06      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.87/1.06      inference('sup+', [status(thm)], ['12', '66'])).
% 0.87/1.06  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('69', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['67', '68'])).
% 0.87/1.06  thf('70', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf(t4_subset_1, axiom,
% 0.87/1.06    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.87/1.06  thf('71', plain,
% 0.87/1.06      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.87/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.87/1.06  thf(t64_subset_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.06       ( ![C:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.06           ( ( ( k3_subset_1 @ A @ B ) = ( k3_subset_1 @ A @ C ) ) =>
% 0.87/1.06             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.87/1.06  thf('72', plain,
% 0.87/1.06      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.87/1.06          | ((X32) = (X30))
% 0.87/1.06          | ((k3_subset_1 @ X31 @ X32) != (k3_subset_1 @ X31 @ X30))
% 0.87/1.06          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t64_subset_1])).
% 0.87/1.06  thf('73', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.87/1.06          | ((k3_subset_1 @ X0 @ X1) != (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.87/1.06          | ((X1) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['71', '72'])).
% 0.87/1.06  thf('74', plain,
% 0.87/1.06      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.87/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.87/1.06  thf('75', plain,
% 0.87/1.06      (![X19 : $i, X20 : $i]:
% 0.87/1.06         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.87/1.06          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.87/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.87/1.06  thf('76', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['74', '75'])).
% 0.87/1.06  thf(t3_boole, axiom,
% 0.87/1.06    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.87/1.06  thf('77', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.87/1.06      inference('cnf', [status(esa)], [t3_boole])).
% 0.87/1.06  thf('78', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.87/1.06      inference('sup+', [status(thm)], ['76', '77'])).
% 0.87/1.06  thf('79', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.87/1.06          | ((k3_subset_1 @ X0 @ X1) != (X0))
% 0.87/1.06          | ((X1) = (k1_xboole_0)))),
% 0.87/1.06      inference('demod', [status(thm)], ['73', '78'])).
% 0.87/1.06  thf('80', plain,
% 0.87/1.06      ((((sk_B) = (k1_xboole_0))
% 0.87/1.06        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) != (u1_struct_0 @ sk_A)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['70', '79'])).
% 0.87/1.06  thf('81', plain, (((sk_B) != (k1_xboole_0))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('82', plain,
% 0.87/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) != (u1_struct_0 @ sk_A))),
% 0.87/1.06      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.87/1.06  thf('83', plain,
% 0.87/1.06      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['25', '40', '46'])).
% 0.87/1.06  thf('84', plain, (((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['82', '83'])).
% 0.87/1.06  thf('85', plain, ($false),
% 0.87/1.06      inference('simplify_reflect-', [status(thm)], ['69', '84'])).
% 0.87/1.06  
% 0.87/1.06  % SZS output end Refutation
% 0.87/1.06  
% 0.87/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
