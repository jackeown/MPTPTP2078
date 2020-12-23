%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sboI1Bh6F8

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:16 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 231 expanded)
%              Number of leaves         :   24 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  694 (2588 expanded)
%              Number of equality atoms :   18 (  60 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_tops_1 @ X25 @ X24 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ X24 ) @ ( k2_pre_topc @ X25 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X10 @ X9 ) @ ( k3_subset_1 @ X10 @ X11 ) )
      | ( r1_tarski @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X13 @ X14 ) @ ( k3_subset_1 @ X13 @ ( k9_subset_1 @ X13 @ X14 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('47',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['35','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sboI1Bh6F8
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.04  % Solved by: fo/fo7.sh
% 0.84/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.04  % done 559 iterations in 0.568s
% 0.84/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.04  % SZS output start Refutation
% 0.84/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.04  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.84/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.04  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.84/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.04  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.84/1.04  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.84/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.04  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.84/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.04  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.84/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.04  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.84/1.04  thf(t69_tops_1, conjecture,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( l1_pre_topc @ A ) =>
% 0.84/1.04       ( ![B:$i]:
% 0.84/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.04           ( ( v4_pre_topc @ B @ A ) =>
% 0.84/1.04             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.84/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.04    (~( ![A:$i]:
% 0.84/1.04        ( ( l1_pre_topc @ A ) =>
% 0.84/1.04          ( ![B:$i]:
% 0.84/1.04            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.04              ( ( v4_pre_topc @ B @ A ) =>
% 0.84/1.04                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.84/1.04    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.84/1.04  thf('0', plain,
% 0.84/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(d2_tops_1, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( l1_pre_topc @ A ) =>
% 0.84/1.04       ( ![B:$i]:
% 0.84/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.04           ( ( k2_tops_1 @ A @ B ) =
% 0.84/1.04             ( k9_subset_1 @
% 0.84/1.04               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.84/1.04               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.84/1.04  thf('1', plain,
% 0.84/1.04      (![X24 : $i, X25 : $i]:
% 0.84/1.04         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.84/1.04          | ((k2_tops_1 @ X25 @ X24)
% 0.84/1.04              = (k9_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.84/1.04                 (k2_pre_topc @ X25 @ X24) @ 
% 0.84/1.04                 (k2_pre_topc @ X25 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24))))
% 0.84/1.04          | ~ (l1_pre_topc @ X25))),
% 0.84/1.04      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.84/1.04  thf('2', plain,
% 0.84/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.84/1.04        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.84/1.04            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.04               (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.84/1.04               (k2_pre_topc @ sk_A @ 
% 0.84/1.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['0', '1'])).
% 0.84/1.04  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('4', plain,
% 0.84/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(t52_pre_topc, axiom,
% 0.84/1.04    (![A:$i]:
% 0.84/1.04     ( ( l1_pre_topc @ A ) =>
% 0.84/1.04       ( ![B:$i]:
% 0.84/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.04           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.84/1.04             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.84/1.04               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.84/1.04  thf('5', plain,
% 0.84/1.04      (![X22 : $i, X23 : $i]:
% 0.84/1.04         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.84/1.04          | ~ (v4_pre_topc @ X22 @ X23)
% 0.84/1.04          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 0.84/1.04          | ~ (l1_pre_topc @ X23))),
% 0.84/1.04      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.84/1.04  thf('6', plain,
% 0.84/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.84/1.04        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.84/1.04        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.84/1.04      inference('sup-', [status(thm)], ['4', '5'])).
% 0.84/1.04  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.84/1.04  thf('10', plain,
% 0.84/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(d5_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.84/1.04  thf('11', plain,
% 0.84/1.04      (![X4 : $i, X5 : $i]:
% 0.84/1.04         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.84/1.04          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.84/1.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.84/1.04  thf('12', plain,
% 0.84/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.84/1.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.84/1.04      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.04  thf('13', plain,
% 0.84/1.04      (((k2_tops_1 @ sk_A @ sk_B)
% 0.84/1.04         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.84/1.04            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.84/1.04      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 0.84/1.04  thf(t36_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.84/1.04  thf('14', plain,
% 0.84/1.04      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.84/1.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.84/1.04  thf(t3_subset, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.84/1.04  thf('15', plain,
% 0.84/1.04      (![X17 : $i, X19 : $i]:
% 0.84/1.04         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.84/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.04  thf('16', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['14', '15'])).
% 0.84/1.04  thf(dt_k2_pre_topc, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( l1_pre_topc @ A ) & 
% 0.84/1.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.04       ( m1_subset_1 @
% 0.84/1.04         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.84/1.04  thf('17', plain,
% 0.84/1.04      (![X20 : $i, X21 : $i]:
% 0.84/1.04         (~ (l1_pre_topc @ X20)
% 0.84/1.04          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.84/1.04          | (m1_subset_1 @ (k2_pre_topc @ X20 @ X21) @ 
% 0.84/1.04             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.84/1.04  thf('18', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         ((m1_subset_1 @ 
% 0.84/1.04           (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.84/1.04           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.84/1.04          | ~ (l1_pre_topc @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['16', '17'])).
% 0.84/1.04  thf(dt_k9_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.84/1.04  thf('19', plain,
% 0.84/1.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.84/1.04         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.84/1.04          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.84/1.04      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.84/1.04  thf('20', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (~ (l1_pre_topc @ X0)
% 0.84/1.04          | (m1_subset_1 @ 
% 0.84/1.04             (k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ 
% 0.84/1.04              (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))) @ 
% 0.84/1.04             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['18', '19'])).
% 0.84/1.04  thf('21', plain,
% 0.84/1.04      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.84/1.04         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.04      inference('sup+', [status(thm)], ['13', '20'])).
% 0.84/1.04  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('23', plain,
% 0.84/1.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.84/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.04      inference('demod', [status(thm)], ['21', '22'])).
% 0.84/1.04  thf('24', plain,
% 0.84/1.04      (![X4 : $i, X5 : $i]:
% 0.84/1.04         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.84/1.04          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.84/1.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.84/1.04  thf('25', plain,
% 0.84/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.84/1.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['23', '24'])).
% 0.84/1.04  thf('26', plain,
% 0.84/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.84/1.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.84/1.04      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.04  thf(t31_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04       ( ![C:$i]:
% 0.84/1.04         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04           ( ( r1_tarski @ B @ C ) <=>
% 0.84/1.04             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.84/1.04  thf('27', plain,
% 0.84/1.04      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.84/1.04         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.84/1.04          | ~ (r1_tarski @ (k3_subset_1 @ X10 @ X9) @ (k3_subset_1 @ X10 @ X11))
% 0.84/1.04          | (r1_tarski @ X11 @ X9)
% 0.84/1.04          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.84/1.04      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.84/1.04  thf('28', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.84/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.04          | (r1_tarski @ X0 @ sk_B)
% 0.84/1.04          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['26', '27'])).
% 0.84/1.04  thf('29', plain,
% 0.84/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('30', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.84/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.04          | (r1_tarski @ X0 @ sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['28', '29'])).
% 0.84/1.04  thf('31', plain,
% 0.84/1.04      ((~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.84/1.04        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.84/1.04        | ~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.84/1.04             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['25', '30'])).
% 0.84/1.04  thf('32', plain,
% 0.84/1.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.84/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.04      inference('demod', [status(thm)], ['21', '22'])).
% 0.84/1.04  thf('33', plain,
% 0.84/1.04      ((~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.84/1.04        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.84/1.04      inference('demod', [status(thm)], ['31', '32'])).
% 0.84/1.04  thf('34', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('35', plain,
% 0.84/1.04      (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.84/1.04      inference('clc', [status(thm)], ['33', '34'])).
% 0.84/1.04  thf('36', plain,
% 0.84/1.04      (((k2_tops_1 @ sk_A @ sk_B)
% 0.84/1.04         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.84/1.04            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.84/1.04      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 0.84/1.04  thf('37', plain,
% 0.84/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('38', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         ((m1_subset_1 @ 
% 0.84/1.04           (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.84/1.04           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.84/1.04          | ~ (l1_pre_topc @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['16', '17'])).
% 0.84/1.04  thf(t42_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04       ( ![C:$i]:
% 0.84/1.04         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04           ( r1_tarski @
% 0.84/1.04             ( k3_subset_1 @ A @ B ) @ 
% 0.84/1.04             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.84/1.04  thf('39', plain,
% 0.84/1.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.04         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.84/1.04          | (r1_tarski @ (k3_subset_1 @ X13 @ X14) @ 
% 0.84/1.04             (k3_subset_1 @ X13 @ (k9_subset_1 @ X13 @ X14 @ X12)))
% 0.84/1.04          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.84/1.04      inference('cnf', [status(esa)], [t42_subset_1])).
% 0.84/1.04  thf('40', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         (~ (l1_pre_topc @ X0)
% 0.84/1.04          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.84/1.04          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X2) @ 
% 0.84/1.04             (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.84/1.04              (k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ 
% 0.84/1.04               (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.84/1.04      inference('sup-', [status(thm)], ['38', '39'])).
% 0.84/1.04  thf('41', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.04            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.84/1.04             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))))
% 0.84/1.04          | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.04      inference('sup-', [status(thm)], ['37', '40'])).
% 0.84/1.04  thf('42', plain,
% 0.84/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.84/1.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.84/1.04      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.04  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('44', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.04           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.84/1.04            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.84/1.04      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.84/1.04  thf('45', plain,
% 0.84/1.04      ((r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.84/1.04      inference('sup+', [status(thm)], ['36', '44'])).
% 0.84/1.04  thf('46', plain,
% 0.84/1.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.84/1.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['23', '24'])).
% 0.84/1.04  thf('47', plain,
% 0.84/1.04      ((r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.84/1.04        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.84/1.04      inference('demod', [status(thm)], ['45', '46'])).
% 0.84/1.04  thf('48', plain, ($false), inference('demod', [status(thm)], ['35', '47'])).
% 0.84/1.04  
% 0.84/1.04  % SZS output end Refutation
% 0.84/1.04  
% 0.84/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
