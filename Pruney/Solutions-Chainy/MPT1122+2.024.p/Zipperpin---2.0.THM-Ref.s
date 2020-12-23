%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gocKTi8Akh

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:22 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 347 expanded)
%              Number of leaves         :   24 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          : 1122 (7255 expanded)
%              Number of equality atoms :   41 ( 288 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t53_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
              & ( ( ( v2_pre_topc @ A )
                  & ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                    = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
               => ( v3_pre_topc @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_pre_topc])).

thf('0',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
            = B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_struct_0 @ X14 ) @ ( k7_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_struct_0 @ X14 ) @ X13 ) )
        = X13 )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t22_pre_topc])).

thf('4',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k2_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('10',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('14',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X3 @ X2 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) )
        = ( k2_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('21',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('23',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf('28',plain,
    ( ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_pre_topc @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['31'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

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

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_pre_topc @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
       != X15 )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
         != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
        | ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X8 @ X9 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k2_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
   <= ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf('50',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('52',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['30','32','52','53'])).

thf('55',plain,(
    v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['28','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( v4_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
   <= ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('63',plain,(
    ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['30','32','52'])).

thf('64',plain,(
    ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gocKTi8Akh
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 184 iterations in 0.147s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.38/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.59  thf(t53_pre_topc, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( ( v3_pre_topc @ B @ A ) =>
% 0.38/0.59               ( ( k2_pre_topc @
% 0.38/0.59                   A @ 
% 0.38/0.59                   ( k7_subset_1 @
% 0.38/0.59                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 0.38/0.59                 ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 0.38/0.59             ( ( ( v2_pre_topc @ A ) & 
% 0.38/0.59                 ( ( k2_pre_topc @
% 0.38/0.59                     A @ 
% 0.38/0.59                     ( k7_subset_1 @
% 0.38/0.59                       ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 0.38/0.59                   ( k7_subset_1 @
% 0.38/0.59                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 0.38/0.59               ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( l1_pre_topc @ A ) =>
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59              ( ( ( v3_pre_topc @ B @ A ) =>
% 0.38/0.59                  ( ( k2_pre_topc @
% 0.38/0.59                      A @ 
% 0.38/0.59                      ( k7_subset_1 @
% 0.38/0.59                        ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 0.38/0.59                    ( k7_subset_1 @
% 0.38/0.59                      ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 0.38/0.59                ( ( ( v2_pre_topc @ A ) & 
% 0.38/0.59                    ( ( k2_pre_topc @
% 0.38/0.59                        A @ 
% 0.38/0.59                        ( k7_subset_1 @
% 0.38/0.59                          ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 0.38/0.59                      ( k7_subset_1 @
% 0.38/0.59                        ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 0.38/0.59                  ( v3_pre_topc @ B @ A ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t53_pre_topc])).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (((v3_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | ((k2_pre_topc @ sk_A @ 
% 0.38/0.59            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.59      inference('split', [status(esa)], ['0'])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t22_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_struct_0 @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( k7_subset_1 @
% 0.38/0.59               ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ 
% 0.38/0.59               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 0.38/0.59             ( B ) ) ) ) ))).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X13 : $i, X14 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.59          | ((k7_subset_1 @ (u1_struct_0 @ X14) @ (k2_struct_0 @ X14) @ 
% 0.38/0.59              (k7_subset_1 @ (u1_struct_0 @ X14) @ (k2_struct_0 @ X14) @ X13))
% 0.38/0.59              = (X13))
% 0.38/0.59          | ~ (l1_struct_0 @ X14))),
% 0.38/0.59      inference('cnf', [status(esa)], [t22_pre_topc])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      ((~ (l1_struct_0 @ sk_A)
% 0.38/0.59        | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59            = (sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.59  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(dt_l1_pre_topc, axiom,
% 0.38/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.59  thf('6', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.59  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.59  thf(d6_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.59             ( v3_pre_topc @
% 0.38/0.59               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.38/0.59               A ) ) ) ) ))).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.59          | ~ (v3_pre_topc @ 
% 0.38/0.59               (k7_subset_1 @ (u1_struct_0 @ X9) @ (k2_struct_0 @ X9) @ X8) @ 
% 0.38/0.59               X9)
% 0.38/0.59          | (v4_pre_topc @ X8 @ X9)
% 0.38/0.59          | ~ (l1_pre_topc @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ 
% 0.38/0.59           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59           sk_A)
% 0.38/0.59        | ~ (m1_subset_1 @ 
% 0.38/0.59             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.59  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(dt_k3_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.59       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(dt_k4_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.59       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.38/0.59          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3))
% 0.38/0.59          | (m1_subset_1 @ (k4_subset_1 @ X3 @ X2 @ X4) @ (k1_zfmisc_1 @ X3)))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      ((m1_subset_1 @ 
% 0.38/0.59        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['14', '17'])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t18_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_struct_0 @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( k4_subset_1 @
% 0.38/0.59               ( u1_struct_0 @ A ) @ B @ 
% 0.38/0.59               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.38/0.59             ( k2_struct_0 @ A ) ) ) ) ))).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (![X11 : $i, X12 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.59          | ((k4_subset_1 @ (u1_struct_0 @ X12) @ X11 @ 
% 0.38/0.59              (k3_subset_1 @ (u1_struct_0 @ X12) @ X11)) = (k2_struct_0 @ X12))
% 0.38/0.59          | ~ (l1_struct_0 @ X12))),
% 0.38/0.59      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      ((~ (l1_struct_0 @ sk_A)
% 0.38/0.59        | ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.59            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (k2_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.59  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (k2_struct_0 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['18', '23'])).
% 0.38/0.59  thf(dt_k7_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.59       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.38/0.59          | (m1_subset_1 @ (k7_subset_1 @ X6 @ X5 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (m1_subset_1 @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ 
% 0.38/0.59           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59           sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['10', '11', '26'])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (((v4_pre_topc @ 
% 0.38/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59         sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '27'])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (~
% 0.38/0.59       (((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))) | 
% 0.38/0.59       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('split', [status(esa)], ['29'])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59        | (v2_pre_topc @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (((v2_pre_topc @ sk_A)) | 
% 0.38/0.59       ~
% 0.38/0.59       (((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('split', [status(esa)], ['31'])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.59         <= ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                 sk_B))
% 0.38/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                   sk_B))))),
% 0.38/0.59      inference('split', [status(esa)], ['0'])).
% 0.38/0.59  thf('34', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.38/0.59      inference('split', [status(esa)], ['31'])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (m1_subset_1 @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.59  thf(t52_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.59          | ~ (v2_pre_topc @ X16)
% 0.38/0.59          | ((k2_pre_topc @ X16 @ X15) != (X15))
% 0.38/0.59          | (v4_pre_topc @ X15 @ X16)
% 0.38/0.59          | ~ (l1_pre_topc @ X16))),
% 0.38/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (v4_pre_topc @ 
% 0.38/0.59             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59             sk_A)
% 0.38/0.59          | ((k2_pre_topc @ sk_A @ 
% 0.38/0.59              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.38/0.59              != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                  X0))
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.59  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v4_pre_topc @ 
% 0.38/0.59           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59           sk_A)
% 0.38/0.59          | ((k2_pre_topc @ sk_A @ 
% 0.38/0.59              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.38/0.59              != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                  X0))
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          (((k2_pre_topc @ sk_A @ 
% 0.38/0.59             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.38/0.59             != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.38/0.59           | (v4_pre_topc @ 
% 0.38/0.59              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59              sk_A)))
% 0.38/0.59         <= (((v2_pre_topc @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['34', '39'])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.38/0.59           != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (v4_pre_topc @ 
% 0.38/0.59            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59            sk_A)))
% 0.38/0.59         <= ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                 sk_B))
% 0.38/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                   sk_B))) & 
% 0.38/0.59             ((v2_pre_topc @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['33', '40'])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (((v4_pre_topc @ 
% 0.38/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59         sk_A))
% 0.38/0.59         <= ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                 sk_B))
% 0.38/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                   sk_B))) & 
% 0.38/0.59             ((v2_pre_topc @ sk_A)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (m1_subset_1 @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.59          | ~ (v4_pre_topc @ X8 @ X9)
% 0.38/0.59          | (v3_pre_topc @ 
% 0.38/0.59             (k7_subset_1 @ (u1_struct_0 @ X9) @ (k2_struct_0 @ X9) @ X8) @ X9)
% 0.38/0.59          | ~ (l1_pre_topc @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (v3_pre_topc @ 
% 0.38/0.59             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0)) @ 
% 0.38/0.59             sk_A)
% 0.38/0.59          | ~ (v4_pre_topc @ 
% 0.38/0.59               (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59               sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.59  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v3_pre_topc @ 
% 0.38/0.59           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0)) @ 
% 0.38/0.59           sk_A)
% 0.38/0.59          | ~ (v4_pre_topc @ 
% 0.38/0.59               (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59               sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['45', '46'])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (((v3_pre_topc @ 
% 0.38/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59         sk_A))
% 0.38/0.59         <= ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                 sk_B))
% 0.38/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                   sk_B))) & 
% 0.38/0.59             ((v2_pre_topc @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['42', '47'])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (((v3_pre_topc @ sk_B @ sk_A))
% 0.38/0.59         <= ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                 sk_B))
% 0.38/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                   sk_B))) & 
% 0.38/0.59             ((v2_pre_topc @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.59      inference('split', [status(esa)], ['29'])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (~
% 0.38/0.59       (((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))) | 
% 0.38/0.59       ~ ((v2_pre_topc @ sk_A)) | ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.38/0.59       (((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('split', [status(esa)], ['0'])).
% 0.38/0.59  thf('54', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('sat_resolution*', [status(thm)], ['30', '32', '52', '53'])).
% 0.38/0.59  thf('55', plain,
% 0.38/0.59      ((v4_pre_topc @ 
% 0.38/0.59        (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59        sk_A)),
% 0.38/0.59      inference('simpl_trail', [status(thm)], ['28', '54'])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (m1_subset_1 @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.59          | ~ (v4_pre_topc @ X15 @ X16)
% 0.38/0.59          | ((k2_pre_topc @ X16 @ X15) = (X15))
% 0.38/0.59          | ~ (l1_pre_topc @ X16))),
% 0.38/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.59  thf('58', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ((k2_pre_topc @ sk_A @ 
% 0.38/0.59              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.38/0.59              = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.38/0.59          | ~ (v4_pre_topc @ 
% 0.38/0.59               (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59               sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.59  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k2_pre_topc @ sk_A @ 
% 0.38/0.59            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.38/0.59            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.38/0.59          | ~ (v4_pre_topc @ 
% 0.38/0.59               (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.38/0.59               sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.59  thf('61', plain,
% 0.38/0.59      (((k2_pre_topc @ sk_A @ 
% 0.38/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['55', '60'])).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      ((((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.59         <= (~
% 0.38/0.59             (((k2_pre_topc @ sk_A @ 
% 0.38/0.59                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                 sk_B))
% 0.38/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59                   sk_B))))),
% 0.38/0.59      inference('split', [status(esa)], ['29'])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      (~
% 0.38/0.59       (((k2_pre_topc @ sk_A @ 
% 0.38/0.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('sat_resolution*', [status(thm)], ['30', '32', '52'])).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      (((k2_pre_topc @ sk_A @ 
% 0.38/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.38/0.59      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.38/0.59  thf('65', plain, ($false),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['61', '64'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
