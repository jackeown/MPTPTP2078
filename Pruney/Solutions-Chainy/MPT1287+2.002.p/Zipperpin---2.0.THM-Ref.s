%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CUhRm0VmVK

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:57 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 159 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  802 (2448 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k7_subset_1 @ X8 @ X9 @ X7 )
        = ( k9_subset_1 @ X8 @ X9 @ ( k3_subset_1 @ X8 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X3 @ X2 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t101_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ( v6_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v6_tops_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v6_tops_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A )
    | ( v6_tops_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('20',plain,
    ( ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A )
    | ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('26',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

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

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v5_tops_1 @ X15 @ X16 )
      | ~ ( v5_tops_1 @ X17 @ X16 )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t108_tops_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ X0 @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v6_tops_1 @ X13 @ X14 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','36'])).

thf('38',plain,
    ( ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v6_tops_1 @ X13 @ X14 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v6_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['38','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k3_subset_1 @ X11 @ ( k7_subset_1 @ X11 @ X12 @ X10 ) )
        = ( k4_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X12 ) @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['22','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CUhRm0VmVK
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.44/1.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.44/1.69  % Solved by: fo/fo7.sh
% 1.44/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.69  % done 996 iterations in 1.233s
% 1.44/1.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.44/1.69  % SZS output start Refutation
% 1.44/1.69  thf(sk_B_type, type, sk_B: $i).
% 1.44/1.69  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.44/1.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.44/1.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.44/1.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.44/1.69  thf(sk_C_type, type, sk_C: $i).
% 1.44/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.44/1.69  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.44/1.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.44/1.69  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 1.44/1.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.44/1.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.44/1.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.44/1.69  thf(t109_tops_1, conjecture,
% 1.44/1.69    (![A:$i]:
% 1.44/1.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.44/1.69       ( ![B:$i]:
% 1.44/1.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.44/1.69           ( ![C:$i]:
% 1.44/1.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.44/1.69               ( ( ( v6_tops_1 @ B @ A ) & ( v6_tops_1 @ C @ A ) ) =>
% 1.44/1.69                 ( v6_tops_1 @
% 1.44/1.69                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 1.44/1.69  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.69    (~( ![A:$i]:
% 1.44/1.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.44/1.69          ( ![B:$i]:
% 1.44/1.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.44/1.69              ( ![C:$i]:
% 1.44/1.69                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.44/1.69                  ( ( ( v6_tops_1 @ B @ A ) & ( v6_tops_1 @ C @ A ) ) =>
% 1.44/1.69                    ( v6_tops_1 @
% 1.44/1.69                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 1.44/1.69    inference('cnf.neg', [status(esa)], [t109_tops_1])).
% 1.44/1.69  thf('0', plain,
% 1.44/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('1', plain,
% 1.44/1.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf(dt_k3_subset_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.69       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.44/1.69  thf('2', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.44/1.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.44/1.69      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.44/1.69  thf('3', plain,
% 1.44/1.69      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.44/1.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('sup-', [status(thm)], ['1', '2'])).
% 1.44/1.69  thf(t32_subset_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.69       ( ![C:$i]:
% 1.44/1.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.69           ( ( k7_subset_1 @ A @ B @ C ) =
% 1.44/1.69             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.44/1.69  thf('4', plain,
% 1.44/1.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 1.44/1.69          | ((k7_subset_1 @ X8 @ X9 @ X7)
% 1.44/1.69              = (k9_subset_1 @ X8 @ X9 @ (k3_subset_1 @ X8 @ X7)))
% 1.44/1.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t32_subset_1])).
% 1.44/1.69  thf('5', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.44/1.69          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.44/1.69              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.44/1.69              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.44/1.69                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.44/1.69      inference('sup-', [status(thm)], ['3', '4'])).
% 1.44/1.69  thf('6', plain,
% 1.44/1.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf(involutiveness_k3_subset_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.69       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.44/1.69  thf('7', plain,
% 1.44/1.69      (![X5 : $i, X6 : $i]:
% 1.44/1.69         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 1.44/1.69          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.44/1.69      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.44/1.69  thf('8', plain,
% 1.44/1.69      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 1.44/1.69      inference('sup-', [status(thm)], ['6', '7'])).
% 1.44/1.69  thf('9', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.44/1.69          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.44/1.69              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.44/1.69              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)))),
% 1.44/1.69      inference('demod', [status(thm)], ['5', '8'])).
% 1.44/1.69  thf('10', plain,
% 1.44/1.69      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.44/1.69         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.44/1.69         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 1.44/1.69      inference('sup-', [status(thm)], ['0', '9'])).
% 1.44/1.69  thf('11', plain,
% 1.44/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf(dt_k7_subset_1, axiom,
% 1.44/1.69    (![A:$i,B:$i,C:$i]:
% 1.44/1.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.69       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.44/1.69  thf('12', plain,
% 1.44/1.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 1.44/1.69          | (m1_subset_1 @ (k7_subset_1 @ X3 @ X2 @ X4) @ (k1_zfmisc_1 @ X3)))),
% 1.44/1.69      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.44/1.69  thf('13', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.44/1.69          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('sup-', [status(thm)], ['11', '12'])).
% 1.44/1.69  thf(t101_tops_1, axiom,
% 1.44/1.69    (![A:$i]:
% 1.44/1.69     ( ( l1_pre_topc @ A ) =>
% 1.44/1.69       ( ![B:$i]:
% 1.44/1.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.44/1.69           ( ( v6_tops_1 @ B @ A ) <=>
% 1.44/1.69             ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.44/1.69  thf('14', plain,
% 1.44/1.69      (![X13 : $i, X14 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.44/1.69          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 1.44/1.69          | (v6_tops_1 @ X13 @ X14)
% 1.44/1.69          | ~ (l1_pre_topc @ X14))),
% 1.44/1.69      inference('cnf', [status(esa)], [t101_tops_1])).
% 1.44/1.69  thf('15', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         (~ (l1_pre_topc @ sk_A)
% 1.44/1.69          | (v6_tops_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.44/1.69             sk_A)
% 1.44/1.69          | ~ (v5_tops_1 @ 
% 1.44/1.69               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 1.44/1.69               sk_A))),
% 1.44/1.69      inference('sup-', [status(thm)], ['13', '14'])).
% 1.44/1.69  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('17', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         ((v6_tops_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ sk_A)
% 1.44/1.69          | ~ (v5_tops_1 @ 
% 1.44/1.69               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69                (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 1.44/1.69               sk_A))),
% 1.44/1.69      inference('demod', [status(thm)], ['15', '16'])).
% 1.44/1.69  thf('18', plain,
% 1.44/1.69      ((~ (v5_tops_1 @ 
% 1.44/1.69           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 1.44/1.69           sk_A)
% 1.44/1.69        | (v6_tops_1 @ 
% 1.44/1.69           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.44/1.69            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.44/1.69           sk_A))),
% 1.44/1.69      inference('sup-', [status(thm)], ['10', '17'])).
% 1.44/1.69  thf('19', plain,
% 1.44/1.69      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.44/1.69         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.44/1.69         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 1.44/1.69      inference('sup-', [status(thm)], ['0', '9'])).
% 1.44/1.69  thf('20', plain,
% 1.44/1.69      ((~ (v5_tops_1 @ 
% 1.44/1.69           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 1.44/1.69           sk_A)
% 1.44/1.69        | (v6_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 1.44/1.69           sk_A))),
% 1.44/1.69      inference('demod', [status(thm)], ['18', '19'])).
% 1.44/1.69  thf('21', plain,
% 1.44/1.69      (~ (v6_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('22', plain,
% 1.44/1.69      (~ (v5_tops_1 @ 
% 1.44/1.69          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 1.44/1.69          sk_A)),
% 1.44/1.69      inference('clc', [status(thm)], ['20', '21'])).
% 1.44/1.69  thf('23', plain,
% 1.44/1.69      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.44/1.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('sup-', [status(thm)], ['1', '2'])).
% 1.44/1.69  thf('24', plain,
% 1.44/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('25', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.44/1.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.44/1.69      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.44/1.69  thf('26', plain,
% 1.44/1.69      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.44/1.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('sup-', [status(thm)], ['24', '25'])).
% 1.44/1.69  thf(t108_tops_1, axiom,
% 1.44/1.69    (![A:$i]:
% 1.44/1.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.44/1.69       ( ![B:$i]:
% 1.44/1.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.44/1.69           ( ![C:$i]:
% 1.44/1.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.44/1.69               ( ( ( v5_tops_1 @ B @ A ) & ( v5_tops_1 @ C @ A ) ) =>
% 1.44/1.69                 ( v5_tops_1 @
% 1.44/1.69                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 1.44/1.69  thf('27', plain,
% 1.44/1.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.44/1.69          | ~ (v5_tops_1 @ X15 @ X16)
% 1.44/1.69          | ~ (v5_tops_1 @ X17 @ X16)
% 1.44/1.69          | (v5_tops_1 @ (k4_subset_1 @ (u1_struct_0 @ X16) @ X15 @ X17) @ X16)
% 1.44/1.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.44/1.69          | ~ (l1_pre_topc @ X16)
% 1.44/1.69          | ~ (v2_pre_topc @ X16))),
% 1.44/1.69      inference('cnf', [status(esa)], [t108_tops_1])).
% 1.44/1.69  thf('28', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         (~ (v2_pre_topc @ sk_A)
% 1.44/1.69          | ~ (l1_pre_topc @ sk_A)
% 1.44/1.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.44/1.69          | (v5_tops_1 @ 
% 1.44/1.69             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 1.44/1.69             sk_A)
% 1.44/1.69          | ~ (v5_tops_1 @ X0 @ sk_A)
% 1.44/1.69          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.44/1.69      inference('sup-', [status(thm)], ['26', '27'])).
% 1.44/1.69  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('31', plain,
% 1.44/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('32', plain,
% 1.44/1.69      (![X13 : $i, X14 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.44/1.69          | ~ (v6_tops_1 @ X13 @ X14)
% 1.44/1.69          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 1.44/1.69          | ~ (l1_pre_topc @ X14))),
% 1.44/1.69      inference('cnf', [status(esa)], [t101_tops_1])).
% 1.44/1.69  thf('33', plain,
% 1.44/1.69      ((~ (l1_pre_topc @ sk_A)
% 1.44/1.69        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.44/1.69        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 1.44/1.69      inference('sup-', [status(thm)], ['31', '32'])).
% 1.44/1.69  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('35', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('36', plain,
% 1.44/1.69      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 1.44/1.69      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.44/1.69  thf('37', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.44/1.69          | (v5_tops_1 @ 
% 1.44/1.69             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 1.44/1.69             sk_A)
% 1.44/1.69          | ~ (v5_tops_1 @ X0 @ sk_A))),
% 1.44/1.69      inference('demod', [status(thm)], ['28', '29', '30', '36'])).
% 1.44/1.69  thf('38', plain,
% 1.44/1.69      ((~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 1.44/1.69        | (v5_tops_1 @ 
% 1.44/1.69           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.44/1.69            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.44/1.69           sk_A))),
% 1.44/1.69      inference('sup-', [status(thm)], ['23', '37'])).
% 1.44/1.69  thf('39', plain,
% 1.44/1.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('40', plain,
% 1.44/1.69      (![X13 : $i, X14 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.44/1.69          | ~ (v6_tops_1 @ X13 @ X14)
% 1.44/1.69          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 1.44/1.69          | ~ (l1_pre_topc @ X14))),
% 1.44/1.69      inference('cnf', [status(esa)], [t101_tops_1])).
% 1.44/1.69  thf('41', plain,
% 1.44/1.69      ((~ (l1_pre_topc @ sk_A)
% 1.44/1.69        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 1.44/1.69        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 1.44/1.69      inference('sup-', [status(thm)], ['39', '40'])).
% 1.44/1.69  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('43', plain, ((v6_tops_1 @ sk_C @ sk_A)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('44', plain,
% 1.44/1.69      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)),
% 1.44/1.69      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.44/1.69  thf('45', plain,
% 1.44/1.69      ((v5_tops_1 @ 
% 1.44/1.69        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.44/1.69         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.44/1.69        sk_A)),
% 1.44/1.69      inference('demod', [status(thm)], ['38', '44'])).
% 1.44/1.69  thf('46', plain,
% 1.44/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('47', plain,
% 1.44/1.69      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.44/1.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.69      inference('sup-', [status(thm)], ['1', '2'])).
% 1.44/1.69  thf(t33_subset_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.69       ( ![C:$i]:
% 1.44/1.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.69           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 1.44/1.69             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 1.44/1.69  thf('48', plain,
% 1.44/1.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.44/1.69          | ((k3_subset_1 @ X11 @ (k7_subset_1 @ X11 @ X12 @ X10))
% 1.44/1.69              = (k4_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X12) @ X10))
% 1.44/1.69          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t33_subset_1])).
% 1.44/1.69  thf('49', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.44/1.69          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.44/1.69               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.44/1.69              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.44/1.69                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.44/1.69      inference('sup-', [status(thm)], ['47', '48'])).
% 1.44/1.69  thf('50', plain,
% 1.44/1.69      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.44/1.69          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.44/1.69         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.44/1.69            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.44/1.69      inference('sup-', [status(thm)], ['46', '49'])).
% 1.44/1.69  thf('51', plain,
% 1.44/1.69      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.44/1.69         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.44/1.69         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 1.44/1.69      inference('sup-', [status(thm)], ['0', '9'])).
% 1.44/1.69  thf('52', plain,
% 1.44/1.69      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 1.44/1.69         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.44/1.69            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.44/1.69      inference('demod', [status(thm)], ['50', '51'])).
% 1.44/1.69  thf('53', plain,
% 1.44/1.69      ((v5_tops_1 @ 
% 1.44/1.69        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.69         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 1.44/1.69        sk_A)),
% 1.44/1.69      inference('demod', [status(thm)], ['45', '52'])).
% 1.44/1.69  thf('54', plain, ($false), inference('demod', [status(thm)], ['22', '53'])).
% 1.44/1.69  
% 1.44/1.69  % SZS output end Refutation
% 1.44/1.69  
% 1.52/1.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
