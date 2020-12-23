%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MZrZr9mcqJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:57 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 117 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  734 (1744 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t109_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v6_tops_1 @ B @ A )
                  & ( v6_tops_1 @ C @ A ) )
               => ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v6_tops_1 @ B @ A )
                    & ( v6_tops_1 @ C @ A ) )
                 => ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t109_tops_1])).

thf('0',plain,(
    ~ ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t108_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v5_tops_1 @ B @ A )
                  & ( v5_tops_1 @ C @ A ) )
               => ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v5_tops_1 @ X15 @ X16 )
      | ~ ( v5_tops_1 @ X17 @ X16 )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t108_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ X0 @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t101_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v6_tops_1 @ X13 @ X14 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','16'])).

thf('18',plain,
    ( ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v6_tops_1 @ X13 @ X14 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v6_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k3_subset_1 @ X11 @ ( k7_subset_1 @ X11 @ X12 @ X10 ) )
        = ( k4_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X12 ) @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k7_subset_1 @ X8 @ X9 @ X7 )
        = ( k9_subset_1 @ X8 @ X9 @ ( k3_subset_1 @ X8 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('37',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['25','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X2 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ( v6_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MZrZr9mcqJ
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.10/2.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.10/2.32  % Solved by: fo/fo7.sh
% 2.10/2.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.10/2.32  % done 1399 iterations in 1.891s
% 2.10/2.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.10/2.32  % SZS output start Refutation
% 2.10/2.32  thf(sk_B_type, type, sk_B: $i).
% 2.10/2.32  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.10/2.32  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.10/2.32  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.10/2.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.10/2.32  thf(sk_C_type, type, sk_C: $i).
% 2.10/2.32  thf(sk_A_type, type, sk_A: $i).
% 2.10/2.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.10/2.32  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 2.10/2.32  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.10/2.32  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 2.10/2.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.10/2.32  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.10/2.32  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.10/2.32  thf(t109_tops_1, conjecture,
% 2.10/2.32    (![A:$i]:
% 2.10/2.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.10/2.32       ( ![B:$i]:
% 2.10/2.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.10/2.32           ( ![C:$i]:
% 2.10/2.32             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.10/2.32               ( ( ( v6_tops_1 @ B @ A ) & ( v6_tops_1 @ C @ A ) ) =>
% 2.10/2.32                 ( v6_tops_1 @
% 2.10/2.32                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 2.10/2.32  thf(zf_stmt_0, negated_conjecture,
% 2.10/2.32    (~( ![A:$i]:
% 2.10/2.32        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.10/2.32          ( ![B:$i]:
% 2.10/2.32            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.10/2.32              ( ![C:$i]:
% 2.10/2.32                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.10/2.32                  ( ( ( v6_tops_1 @ B @ A ) & ( v6_tops_1 @ C @ A ) ) =>
% 2.10/2.32                    ( v6_tops_1 @
% 2.10/2.32                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 2.10/2.32    inference('cnf.neg', [status(esa)], [t109_tops_1])).
% 2.10/2.32  thf('0', plain,
% 2.10/2.32      (~ (v6_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('1', plain,
% 2.10/2.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf(dt_k3_subset_1, axiom,
% 2.10/2.32    (![A:$i,B:$i]:
% 2.10/2.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.10/2.32       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.10/2.32  thf('2', plain,
% 2.10/2.32      (![X0 : $i, X1 : $i]:
% 2.10/2.32         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 2.10/2.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 2.10/2.32      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.10/2.32  thf('3', plain,
% 2.10/2.32      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.10/2.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('sup-', [status(thm)], ['1', '2'])).
% 2.10/2.32  thf('4', plain,
% 2.10/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('5', plain,
% 2.10/2.32      (![X0 : $i, X1 : $i]:
% 2.10/2.32         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 2.10/2.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 2.10/2.32      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.10/2.32  thf('6', plain,
% 2.10/2.32      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.10/2.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('sup-', [status(thm)], ['4', '5'])).
% 2.10/2.32  thf(t108_tops_1, axiom,
% 2.10/2.32    (![A:$i]:
% 2.10/2.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.10/2.32       ( ![B:$i]:
% 2.10/2.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.10/2.32           ( ![C:$i]:
% 2.10/2.32             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.10/2.32               ( ( ( v5_tops_1 @ B @ A ) & ( v5_tops_1 @ C @ A ) ) =>
% 2.10/2.32                 ( v5_tops_1 @
% 2.10/2.32                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 2.10/2.32  thf('7', plain,
% 2.10/2.32      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 2.10/2.32          | ~ (v5_tops_1 @ X15 @ X16)
% 2.10/2.32          | ~ (v5_tops_1 @ X17 @ X16)
% 2.10/2.32          | (v5_tops_1 @ (k4_subset_1 @ (u1_struct_0 @ X16) @ X15 @ X17) @ X16)
% 2.10/2.32          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 2.10/2.32          | ~ (l1_pre_topc @ X16)
% 2.10/2.32          | ~ (v2_pre_topc @ X16))),
% 2.10/2.32      inference('cnf', [status(esa)], [t108_tops_1])).
% 2.10/2.32  thf('8', plain,
% 2.10/2.32      (![X0 : $i]:
% 2.10/2.32         (~ (v2_pre_topc @ sk_A)
% 2.10/2.32          | ~ (l1_pre_topc @ sk_A)
% 2.10/2.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.10/2.32          | (v5_tops_1 @ 
% 2.10/2.32             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 2.10/2.32             sk_A)
% 2.10/2.32          | ~ (v5_tops_1 @ X0 @ sk_A)
% 2.10/2.32          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 2.10/2.32      inference('sup-', [status(thm)], ['6', '7'])).
% 2.10/2.32  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('11', plain,
% 2.10/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf(t101_tops_1, axiom,
% 2.10/2.32    (![A:$i]:
% 2.10/2.32     ( ( l1_pre_topc @ A ) =>
% 2.10/2.32       ( ![B:$i]:
% 2.10/2.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.10/2.32           ( ( v6_tops_1 @ B @ A ) <=>
% 2.10/2.32             ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 2.10/2.32  thf('12', plain,
% 2.10/2.32      (![X13 : $i, X14 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 2.10/2.32          | ~ (v6_tops_1 @ X13 @ X14)
% 2.10/2.32          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 2.10/2.32          | ~ (l1_pre_topc @ X14))),
% 2.10/2.32      inference('cnf', [status(esa)], [t101_tops_1])).
% 2.10/2.32  thf('13', plain,
% 2.10/2.32      ((~ (l1_pre_topc @ sk_A)
% 2.10/2.32        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 2.10/2.32        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 2.10/2.32      inference('sup-', [status(thm)], ['11', '12'])).
% 2.10/2.32  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('15', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('16', plain,
% 2.10/2.32      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 2.10/2.32      inference('demod', [status(thm)], ['13', '14', '15'])).
% 2.10/2.32  thf('17', plain,
% 2.10/2.32      (![X0 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.10/2.32          | (v5_tops_1 @ 
% 2.10/2.32             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 2.10/2.32             sk_A)
% 2.10/2.32          | ~ (v5_tops_1 @ X0 @ sk_A))),
% 2.10/2.32      inference('demod', [status(thm)], ['8', '9', '10', '16'])).
% 2.10/2.32  thf('18', plain,
% 2.10/2.32      ((~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 2.10/2.32        | (v5_tops_1 @ 
% 2.10/2.32           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.10/2.32            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 2.10/2.32           sk_A))),
% 2.10/2.32      inference('sup-', [status(thm)], ['3', '17'])).
% 2.10/2.32  thf('19', plain,
% 2.10/2.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('20', plain,
% 2.10/2.32      (![X13 : $i, X14 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 2.10/2.32          | ~ (v6_tops_1 @ X13 @ X14)
% 2.10/2.32          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 2.10/2.32          | ~ (l1_pre_topc @ X14))),
% 2.10/2.32      inference('cnf', [status(esa)], [t101_tops_1])).
% 2.10/2.32  thf('21', plain,
% 2.10/2.32      ((~ (l1_pre_topc @ sk_A)
% 2.10/2.32        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 2.10/2.32        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 2.10/2.32      inference('sup-', [status(thm)], ['19', '20'])).
% 2.10/2.32  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('23', plain, ((v6_tops_1 @ sk_C @ sk_A)),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('24', plain,
% 2.10/2.32      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)),
% 2.10/2.32      inference('demod', [status(thm)], ['21', '22', '23'])).
% 2.10/2.32  thf('25', plain,
% 2.10/2.32      ((v5_tops_1 @ 
% 2.10/2.32        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.10/2.32         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 2.10/2.32        sk_A)),
% 2.10/2.32      inference('demod', [status(thm)], ['18', '24'])).
% 2.10/2.32  thf('26', plain,
% 2.10/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('27', plain,
% 2.10/2.32      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.10/2.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('sup-', [status(thm)], ['1', '2'])).
% 2.10/2.32  thf(t33_subset_1, axiom,
% 2.10/2.32    (![A:$i,B:$i]:
% 2.10/2.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.10/2.32       ( ![C:$i]:
% 2.10/2.32         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.10/2.32           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.10/2.32             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 2.10/2.32  thf('28', plain,
% 2.10/2.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 2.10/2.32          | ((k3_subset_1 @ X11 @ (k7_subset_1 @ X11 @ X12 @ X10))
% 2.10/2.32              = (k4_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X12) @ X10))
% 2.10/2.32          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 2.10/2.32      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.10/2.32  thf('29', plain,
% 2.10/2.32      (![X0 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.10/2.32          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.10/2.32               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 2.10/2.32              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 2.10/2.32                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 2.10/2.32      inference('sup-', [status(thm)], ['27', '28'])).
% 2.10/2.32  thf('30', plain,
% 2.10/2.32      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.10/2.32          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 2.10/2.32         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.10/2.32            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 2.10/2.32      inference('sup-', [status(thm)], ['26', '29'])).
% 2.10/2.32  thf('31', plain,
% 2.10/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('32', plain,
% 2.10/2.32      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.10/2.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('sup-', [status(thm)], ['1', '2'])).
% 2.10/2.32  thf(t32_subset_1, axiom,
% 2.10/2.32    (![A:$i,B:$i]:
% 2.10/2.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.10/2.32       ( ![C:$i]:
% 2.10/2.32         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.10/2.32           ( ( k7_subset_1 @ A @ B @ C ) =
% 2.10/2.32             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.10/2.32  thf('33', plain,
% 2.10/2.32      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.10/2.32          | ((k7_subset_1 @ X8 @ X9 @ X7)
% 2.10/2.32              = (k9_subset_1 @ X8 @ X9 @ (k3_subset_1 @ X8 @ X7)))
% 2.10/2.32          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 2.10/2.32      inference('cnf', [status(esa)], [t32_subset_1])).
% 2.10/2.32  thf('34', plain,
% 2.10/2.32      (![X0 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.10/2.32          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.10/2.32              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 2.10/2.32              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.10/2.32                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 2.10/2.32      inference('sup-', [status(thm)], ['32', '33'])).
% 2.10/2.32  thf('35', plain,
% 2.10/2.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf(involutiveness_k3_subset_1, axiom,
% 2.10/2.32    (![A:$i,B:$i]:
% 2.10/2.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.10/2.32       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.10/2.32  thf('36', plain,
% 2.10/2.32      (![X5 : $i, X6 : $i]:
% 2.10/2.32         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 2.10/2.32          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 2.10/2.32      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.10/2.32  thf('37', plain,
% 2.10/2.32      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 2.10/2.32      inference('sup-', [status(thm)], ['35', '36'])).
% 2.10/2.32  thf('38', plain,
% 2.10/2.32      (![X0 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.10/2.32          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.10/2.32              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 2.10/2.32              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)))),
% 2.10/2.32      inference('demod', [status(thm)], ['34', '37'])).
% 2.10/2.32  thf('39', plain,
% 2.10/2.32      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.10/2.32         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 2.10/2.32         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 2.10/2.32      inference('sup-', [status(thm)], ['31', '38'])).
% 2.10/2.32  thf('40', plain,
% 2.10/2.32      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 2.10/2.32         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.10/2.32            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 2.10/2.32      inference('demod', [status(thm)], ['30', '39'])).
% 2.10/2.32  thf('41', plain,
% 2.10/2.32      ((v5_tops_1 @ 
% 2.10/2.32        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 2.10/2.32        sk_A)),
% 2.10/2.32      inference('demod', [status(thm)], ['25', '40'])).
% 2.10/2.32  thf('42', plain,
% 2.10/2.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf(dt_k9_subset_1, axiom,
% 2.10/2.32    (![A:$i,B:$i,C:$i]:
% 2.10/2.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.10/2.32       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.10/2.32  thf('43', plain,
% 2.10/2.32      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.10/2.32         ((m1_subset_1 @ (k9_subset_1 @ X2 @ X3 @ X4) @ (k1_zfmisc_1 @ X2))
% 2.10/2.32          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X2)))),
% 2.10/2.32      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 2.10/2.32  thf('44', plain,
% 2.10/2.32      (![X0 : $i]:
% 2.10/2.32         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 2.10/2.32          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.10/2.32      inference('sup-', [status(thm)], ['42', '43'])).
% 2.10/2.32  thf('45', plain,
% 2.10/2.32      (![X13 : $i, X14 : $i]:
% 2.10/2.32         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 2.10/2.32          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 2.10/2.32          | (v6_tops_1 @ X13 @ X14)
% 2.10/2.32          | ~ (l1_pre_topc @ X14))),
% 2.10/2.32      inference('cnf', [status(esa)], [t101_tops_1])).
% 2.10/2.32  thf('46', plain,
% 2.10/2.32      (![X0 : $i]:
% 2.10/2.32         (~ (l1_pre_topc @ sk_A)
% 2.10/2.32          | (v6_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 2.10/2.32             sk_A)
% 2.10/2.32          | ~ (v5_tops_1 @ 
% 2.10/2.32               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32                (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)) @ 
% 2.10/2.32               sk_A))),
% 2.10/2.32      inference('sup-', [status(thm)], ['44', '45'])).
% 2.10/2.32  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 2.10/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.10/2.32  thf('48', plain,
% 2.10/2.32      (![X0 : $i]:
% 2.10/2.32         ((v6_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ sk_A)
% 2.10/2.32          | ~ (v5_tops_1 @ 
% 2.10/2.32               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.10/2.32                (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)) @ 
% 2.10/2.32               sk_A))),
% 2.10/2.32      inference('demod', [status(thm)], ['46', '47'])).
% 2.10/2.32  thf('49', plain,
% 2.10/2.32      ((v6_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 2.10/2.32      inference('sup-', [status(thm)], ['41', '48'])).
% 2.10/2.32  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 2.10/2.32  
% 2.10/2.32  % SZS output end Refutation
% 2.10/2.32  
% 2.10/2.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
