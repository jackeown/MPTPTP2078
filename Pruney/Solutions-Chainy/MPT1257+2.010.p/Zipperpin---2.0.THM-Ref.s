%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bHDgfdAflq

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:19 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 200 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  835 (2219 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t73_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tops_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k1_tops_1 @ X13 @ X12 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_pre_topc @ X13 @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X5 @ X6 ) @ ( k3_subset_1 @ X5 @ ( k9_subset_1 @ X5 @ X6 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_tops_1 @ X15 @ X14 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k2_pre_topc @ X15 @ X14 ) @ ( k2_pre_topc @ X15 @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ X18 )
        = ( k2_tops_1 @ X19 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('42',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('45',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('47',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','42','47'])).

thf('49',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','28','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X9 @ ( k3_subset_1 @ X8 @ X7 ) )
      | ( r1_xboole_0 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('59',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bHDgfdAflq
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 526 iterations in 0.719s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.99/1.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.17  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.99/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.17  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.99/1.17  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.99/1.17  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.99/1.17  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(t73_tops_1, conjecture,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.17    (~( ![A:$i]:
% 0.99/1.17        ( ( l1_pre_topc @ A ) =>
% 0.99/1.17          ( ![B:$i]:
% 0.99/1.17            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17              ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t73_tops_1])).
% 0.99/1.17  thf('0', plain,
% 0.99/1.17      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('1', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(dt_k3_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.99/1.17  thf('2', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.99/1.17  thf('3', plain,
% 0.99/1.17      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['1', '2'])).
% 0.99/1.17  thf(dt_k2_pre_topc, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17       ( m1_subset_1 @
% 0.99/1.17         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.99/1.17  thf('4', plain,
% 0.99/1.17      (![X10 : $i, X11 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X10)
% 0.99/1.17          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.99/1.17          | (m1_subset_1 @ (k2_pre_topc @ X10 @ X11) @ 
% 0.99/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (((m1_subset_1 @ 
% 0.99/1.17         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.99/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['3', '4'])).
% 0.99/1.17  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('7', plain,
% 0.99/1.17      ((m1_subset_1 @ 
% 0.99/1.17        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['5', '6'])).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      ((m1_subset_1 @ 
% 0.99/1.17        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['7', '8'])).
% 0.99/1.17  thf('10', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(d1_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( k1_tops_1 @ A @ B ) =
% 0.99/1.17             ( k3_subset_1 @
% 0.99/1.17               ( u1_struct_0 @ A ) @ 
% 0.99/1.17               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.99/1.17  thf('11', plain,
% 0.99/1.17      (![X12 : $i, X13 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.99/1.17          | ((k1_tops_1 @ X13 @ X12)
% 0.99/1.17              = (k3_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.99/1.17                 (k2_pre_topc @ X13 @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12))))
% 0.99/1.17          | ~ (l1_pre_topc @ X13))),
% 0.99/1.17      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.99/1.17  thf('12', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.99/1.17            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17               (k2_pre_topc @ sk_A @ 
% 0.99/1.17                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['10', '11'])).
% 0.99/1.17  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('14', plain,
% 0.99/1.17      (((k1_tops_1 @ sk_A @ sk_B)
% 0.99/1.17         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.99/1.17      inference('demod', [status(thm)], ['12', '13'])).
% 0.99/1.17  thf('15', plain,
% 0.99/1.17      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['9', '14'])).
% 0.99/1.17  thf('16', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      ((m1_subset_1 @ 
% 0.99/1.17        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['15', '16'])).
% 0.99/1.17  thf('18', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('19', plain,
% 0.99/1.17      (![X10 : $i, X11 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X10)
% 0.99/1.17          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.99/1.17          | (m1_subset_1 @ (k2_pre_topc @ X10 @ X11) @ 
% 0.99/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.99/1.17  thf('20', plain,
% 0.99/1.17      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.17  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('22', plain,
% 0.99/1.17      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['20', '21'])).
% 0.99/1.17  thf(t42_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ![C:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17           ( r1_tarski @
% 0.99/1.17             ( k3_subset_1 @ A @ B ) @ 
% 0.99/1.17             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.99/1.17  thf('23', plain,
% 0.99/1.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.99/1.17          | (r1_tarski @ (k3_subset_1 @ X5 @ X6) @ 
% 0.99/1.17             (k3_subset_1 @ X5 @ (k9_subset_1 @ X5 @ X6 @ X4)))
% 0.99/1.17          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t42_subset_1])).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.99/1.17             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.99/1.17               (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['22', '23'])).
% 0.99/1.17  thf('25', plain,
% 0.99/1.17      ((r1_tarski @ 
% 0.99/1.17        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.99/1.17        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.17          (k2_pre_topc @ sk_A @ sk_B))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['17', '24'])).
% 0.99/1.17  thf('26', plain,
% 0.99/1.17      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['9', '14'])).
% 0.99/1.17  thf(involutiveness_k3_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.99/1.17  thf('27', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i]:
% 0.99/1.17         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.99/1.17      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.99/1.17  thf('28', plain,
% 0.99/1.17      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.17         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['26', '27'])).
% 0.99/1.17  thf('29', plain,
% 0.99/1.17      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['1', '2'])).
% 0.99/1.17  thf(d2_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.17             ( k9_subset_1 @
% 0.99/1.17               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.99/1.17               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.99/1.17  thf('30', plain,
% 0.99/1.17      (![X14 : $i, X15 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.99/1.17          | ((k2_tops_1 @ X15 @ X14)
% 0.99/1.17              = (k9_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.99/1.17                 (k2_pre_topc @ X15 @ X14) @ 
% 0.99/1.17                 (k2_pre_topc @ X15 @ (k3_subset_1 @ (u1_struct_0 @ X15) @ X14))))
% 0.99/1.17          | ~ (l1_pre_topc @ X15))),
% 0.99/1.17      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.99/1.17  thf('31', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.99/1.17            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17               (k2_pre_topc @ sk_A @ 
% 0.99/1.17                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.99/1.17               (k2_pre_topc @ sk_A @ 
% 0.99/1.17                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.99/1.17  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('33', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('34', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i]:
% 0.99/1.17         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.99/1.17      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.99/1.17  thf('35', plain,
% 0.99/1.17      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['33', '34'])).
% 0.99/1.17  thf('36', plain,
% 0.99/1.17      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.99/1.17         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.99/1.17            (k2_pre_topc @ sk_A @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.99/1.17  thf('37', plain,
% 0.99/1.17      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['1', '2'])).
% 0.99/1.17  thf(t62_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.17             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.99/1.17  thf('38', plain,
% 0.99/1.17      (![X18 : $i, X19 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.99/1.17          | ((k2_tops_1 @ X19 @ X18)
% 0.99/1.17              = (k2_tops_1 @ X19 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18)))
% 0.99/1.17          | ~ (l1_pre_topc @ X19))),
% 0.99/1.17      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.99/1.17  thf('39', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.99/1.17            = (k2_tops_1 @ sk_A @ 
% 0.99/1.17               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['37', '38'])).
% 0.99/1.17  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('41', plain,
% 0.99/1.17      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['33', '34'])).
% 0.99/1.17  thf('42', plain,
% 0.99/1.17      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.99/1.17         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.99/1.17  thf('43', plain,
% 0.99/1.17      ((m1_subset_1 @ 
% 0.99/1.17        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['5', '6'])).
% 0.99/1.17  thf('44', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i]:
% 0.99/1.17         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.99/1.17      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.99/1.17  thf('45', plain,
% 0.99/1.17      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.99/1.17         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['43', '44'])).
% 0.99/1.17  thf('46', plain,
% 0.99/1.17      (((k1_tops_1 @ sk_A @ sk_B)
% 0.99/1.17         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.99/1.17      inference('demod', [status(thm)], ['12', '13'])).
% 0.99/1.17  thf('47', plain,
% 0.99/1.17      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.17         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['45', '46'])).
% 0.99/1.17  thf('48', plain,
% 0.99/1.17      (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.17         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.17            (k2_pre_topc @ sk_A @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['36', '42', '47'])).
% 0.99/1.17  thf('49', plain,
% 0.99/1.17      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.17        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('demod', [status(thm)], ['25', '28', '48'])).
% 0.99/1.17  thf('50', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(dt_k2_tops_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17       ( m1_subset_1 @
% 0.99/1.17         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.99/1.17  thf('51', plain,
% 0.99/1.17      (![X16 : $i, X17 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X16)
% 0.99/1.17          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.99/1.17          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 0.99/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.99/1.17  thf('52', plain,
% 0.99/1.17      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['50', '51'])).
% 0.99/1.17  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('54', plain,
% 0.99/1.17      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['52', '53'])).
% 0.99/1.17  thf(t43_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ![C:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.99/1.17             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.99/1.17  thf('55', plain,
% 0.99/1.17      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.99/1.17          | ~ (r1_tarski @ X9 @ (k3_subset_1 @ X8 @ X7))
% 0.99/1.17          | (r1_xboole_0 @ X9 @ X7)
% 0.99/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.99/1.17  thf('56', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17          | ~ (r1_tarski @ X0 @ 
% 0.99/1.17               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['54', '55'])).
% 0.99/1.17  thf('57', plain,
% 0.99/1.17      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.17        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['49', '56'])).
% 0.99/1.17  thf('58', plain,
% 0.99/1.17      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['9', '14'])).
% 0.99/1.17  thf('59', plain,
% 0.99/1.17      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['57', '58'])).
% 0.99/1.17  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 0.99/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
