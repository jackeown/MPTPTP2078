%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YGqCmnvpSq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:16 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 244 expanded)
%              Number of leaves         :   25 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  717 (2704 expanded)
%              Number of equality atoms :   23 (  84 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_tops_1 @ X24 @ X23 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_pre_topc @ X24 @ X23 ) @ ( k2_pre_topc @ X24 @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','9','14'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
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
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k6_subset_1 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X12 @ X11 ) @ ( k3_subset_1 @ X12 @ X13 ) )
      | ( r1_tarski @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','9','14'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X15 @ X16 ) @ ( k3_subset_1 @ X15 @ ( k9_subset_1 @ X15 @ X16 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('49',plain,(
    r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['37','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YGqCmnvpSq
% 0.14/0.37  % Computer   : n004.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:18:54 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.76/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.94  % Solved by: fo/fo7.sh
% 0.76/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.94  % done 293 iterations in 0.465s
% 0.76/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.94  % SZS output start Refutation
% 0.76/0.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.94  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.76/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.94  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.76/0.94  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.76/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.94  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.76/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.94  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/0.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.94  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.94  thf(t69_tops_1, conjecture,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( l1_pre_topc @ A ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94           ( ( v4_pre_topc @ B @ A ) =>
% 0.76/0.94             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.94    (~( ![A:$i]:
% 0.76/0.94        ( ( l1_pre_topc @ A ) =>
% 0.76/0.94          ( ![B:$i]:
% 0.76/0.94            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94              ( ( v4_pre_topc @ B @ A ) =>
% 0.76/0.94                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.76/0.94    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.76/0.94  thf('0', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(d2_tops_1, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( l1_pre_topc @ A ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94           ( ( k2_tops_1 @ A @ B ) =
% 0.76/0.94             ( k9_subset_1 @
% 0.76/0.94               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.76/0.94               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.76/0.94  thf('1', plain,
% 0.76/0.94      (![X23 : $i, X24 : $i]:
% 0.76/0.94         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.94          | ((k2_tops_1 @ X24 @ X23)
% 0.76/0.94              = (k9_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.76/0.94                 (k2_pre_topc @ X24 @ X23) @ 
% 0.76/0.94                 (k2_pre_topc @ X24 @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23))))
% 0.76/0.94          | ~ (l1_pre_topc @ X24))),
% 0.76/0.94      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.76/0.94  thf('2', plain,
% 0.76/0.94      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.94        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.94            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.94               (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.76/0.94               (k2_pre_topc @ sk_A @ 
% 0.76/0.94                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.94  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('4', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(t52_pre_topc, axiom,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( l1_pre_topc @ A ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.94           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.76/0.94             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.76/0.94               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.76/0.94  thf('5', plain,
% 0.76/0.94      (![X21 : $i, X22 : $i]:
% 0.76/0.94         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.76/0.94          | ~ (v4_pre_topc @ X21 @ X22)
% 0.76/0.94          | ((k2_pre_topc @ X22 @ X21) = (X21))
% 0.76/0.94          | ~ (l1_pre_topc @ X22))),
% 0.76/0.94      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.76/0.94  thf('6', plain,
% 0.76/0.94      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.94        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.76/0.94        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.94      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.94  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.76/0.94  thf('10', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(d5_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.94       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.76/0.94  thf('11', plain,
% 0.76/0.94      (![X2 : $i, X3 : $i]:
% 0.76/0.94         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.76/0.94          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.94  thf('12', plain,
% 0.76/0.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.76/0.94         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.76/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/0.94  thf(redefinition_k6_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.94  thf('13', plain,
% 0.76/0.94      (![X9 : $i, X10 : $i]:
% 0.76/0.94         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.76/0.94      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.94  thf('14', plain,
% 0.76/0.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.76/0.94         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['12', '13'])).
% 0.76/0.94  thf('15', plain,
% 0.76/0.94      (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.94         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.94            (k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.76/0.94      inference('demod', [status(thm)], ['2', '3', '9', '14'])).
% 0.76/0.94  thf(dt_k6_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.94  thf('16', plain,
% 0.76/0.94      (![X4 : $i, X5 : $i]:
% 0.76/0.94         (m1_subset_1 @ (k6_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.76/0.94  thf(dt_k2_pre_topc, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( l1_pre_topc @ A ) & 
% 0.76/0.94         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.94       ( m1_subset_1 @
% 0.76/0.94         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/0.94  thf('17', plain,
% 0.76/0.94      (![X19 : $i, X20 : $i]:
% 0.76/0.94         (~ (l1_pre_topc @ X19)
% 0.76/0.94          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.76/0.94          | (m1_subset_1 @ (k2_pre_topc @ X19 @ X20) @ 
% 0.76/0.94             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.76/0.94  thf('18', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((m1_subset_1 @ 
% 0.76/0.94           (k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.76/0.94           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.76/0.94          | ~ (l1_pre_topc @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.94  thf(dt_k9_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i,C:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.94       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.94  thf('19', plain,
% 0.76/0.94      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.94         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.76/0.94          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.76/0.94  thf('20', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         (~ (l1_pre_topc @ X0)
% 0.76/0.94          | (m1_subset_1 @ 
% 0.76/0.94             (k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ 
% 0.76/0.94              (k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1))) @ 
% 0.76/0.94             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.94  thf('21', plain,
% 0.76/0.94      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.94         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.94        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['15', '20'])).
% 0.76/0.94  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('23', plain,
% 0.76/0.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.94  thf('24', plain,
% 0.76/0.94      (![X2 : $i, X3 : $i]:
% 0.76/0.94         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.76/0.94          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.94  thf('25', plain,
% 0.76/0.94      (![X9 : $i, X10 : $i]:
% 0.76/0.94         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.76/0.94      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.94  thf('26', plain,
% 0.76/0.94      (![X2 : $i, X3 : $i]:
% 0.76/0.94         (((k3_subset_1 @ X2 @ X3) = (k6_subset_1 @ X2 @ X3))
% 0.76/0.94          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.76/0.94      inference('demod', [status(thm)], ['24', '25'])).
% 0.76/0.94  thf('27', plain,
% 0.76/0.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.76/0.94         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['23', '26'])).
% 0.76/0.94  thf('28', plain,
% 0.76/0.94      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.76/0.94         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['12', '13'])).
% 0.76/0.94  thf(t31_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.94       ( ![C:$i]:
% 0.76/0.94         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.94           ( ( r1_tarski @ B @ C ) <=>
% 0.76/0.94             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.76/0.94  thf('29', plain,
% 0.76/0.94      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.76/0.94         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.76/0.94          | ~ (r1_tarski @ (k3_subset_1 @ X12 @ X11) @ 
% 0.76/0.94               (k3_subset_1 @ X12 @ X13))
% 0.76/0.94          | (r1_tarski @ X13 @ X11)
% 0.76/0.94          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.76/0.94      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.76/0.94  thf('30', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.94             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.94          | (r1_tarski @ X0 @ sk_B)
% 0.76/0.94          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.94  thf('31', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('32', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.94             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.94          | (r1_tarski @ X0 @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['30', '31'])).
% 0.76/0.94  thf('33', plain,
% 0.76/0.94      ((~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.94           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.76/0.94        | ~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.94             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['27', '32'])).
% 0.76/0.94  thf('34', plain,
% 0.76/0.94      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.94  thf('35', plain,
% 0.76/0.94      ((~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.94           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.76/0.94        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.76/0.94      inference('demod', [status(thm)], ['33', '34'])).
% 0.76/0.94  thf('36', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('37', plain,
% 0.76/0.94      (~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.94          (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.94      inference('clc', [status(thm)], ['35', '36'])).
% 0.76/0.94  thf('38', plain,
% 0.76/0.94      (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.94         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.94            (k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.76/0.94      inference('demod', [status(thm)], ['2', '3', '9', '14'])).
% 0.76/0.94  thf('39', plain,
% 0.76/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('40', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((m1_subset_1 @ 
% 0.76/0.94           (k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.76/0.94           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.76/0.94          | ~ (l1_pre_topc @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.94  thf(t42_subset_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.95       ( ![C:$i]:
% 0.76/0.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.95           ( r1_tarski @
% 0.76/0.95             ( k3_subset_1 @ A @ B ) @ 
% 0.76/0.95             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.95  thf('41', plain,
% 0.76/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.76/0.95          | (r1_tarski @ (k3_subset_1 @ X15 @ X16) @ 
% 0.76/0.95             (k3_subset_1 @ X15 @ (k9_subset_1 @ X15 @ X16 @ X14)))
% 0.76/0.95          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t42_subset_1])).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (~ (l1_pre_topc @ X0)
% 0.76/0.95          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.76/0.95          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X2) @ 
% 0.76/0.95             (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.76/0.95              (k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ 
% 0.76/0.95               (k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['40', '41'])).
% 0.76/0.95  thf('43', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.95           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.95            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.95             (k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))
% 0.76/0.95          | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['39', '42'])).
% 0.76/0.95  thf('44', plain,
% 0.76/0.95      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.76/0.95         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['12', '13'])).
% 0.76/0.95  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('46', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.95          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.95           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.95            (k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.95      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.76/0.95  thf('47', plain,
% 0.76/0.95      ((r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.95        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['38', '46'])).
% 0.76/0.95  thf('48', plain,
% 0.76/0.95      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.76/0.95         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['23', '26'])).
% 0.76/0.95  thf('49', plain,
% 0.76/0.95      ((r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.76/0.95        (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['47', '48'])).
% 0.76/0.95  thf('50', plain, ($false), inference('demod', [status(thm)], ['37', '49'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
