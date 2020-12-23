%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SnXsW0DSkp

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 585 expanded)
%              Number of leaves         :   29 ( 179 expanded)
%              Depth                    :   15
%              Number of atoms          : 1015 (8682 expanded)
%              Number of equality atoms :    4 (  27 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t61_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( ( v3_pre_topc @ B @ A )
                | ( v4_pre_topc @ B @ A ) )
              & ( v3_tex_2 @ B @ A )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( ( v3_pre_topc @ B @ A )
                  | ( v4_pre_topc @ B @ A ) )
                & ( v3_tex_2 @ B @ A )
                & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc6_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( v1_xboole_0 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v3_tops_1 @ X6 @ X7 )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc6_tops_1])).

thf('4',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_subset_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( v1_subset_1 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tex_2])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( v1_subset_1 @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['12','17'])).

thf('19',plain,
    ( ~ ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['7','18'])).

thf('20',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_tdlat_3 @ X18 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_tops_1 @ X20 @ X21 )
      | ~ ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ( v2_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf('48',plain,
    ( ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t93_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v2_tops_1 @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_tops_1 @ X12 @ X13 )
      | ~ ( v4_pre_topc @ X12 @ X13 )
      | ~ ( v2_tops_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t93_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('56',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ X11 )
      | ( v4_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('61',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['54','62'])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('65',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('66',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf('68',plain,
    ( ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('70',plain,
    ( ( ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('72',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('73',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ~ ( v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['7','18'])).

thf('76',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('78',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('79',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_tdlat_3 @ X18 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('80',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['76','85'])).

thf('87',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('88',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['63','88'])).

thf('90',plain,(
    ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','89'])).

thf('91',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('92',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('93',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('95',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['90','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SnXsW0DSkp
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 126 iterations in 0.071s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.49  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(t61_tex_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.49         ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.49                ( v3_tex_2 @ B @ A ) & 
% 0.21/0.49                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.49                   ( v3_tex_2 @ B @ A ) & 
% 0.21/0.49                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(cc6_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.21/0.49             ( v1_xboole_0 @ B ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.49          | (v1_xboole_0 @ X6)
% 0.21/0.49          | ~ (v3_tops_1 @ X6 @ X7)
% 0.21/0.49          | ~ (v3_pre_topc @ X6 @ X7)
% 0.21/0.49          | ~ (l1_pre_topc @ X7)
% 0.21/0.49          | ~ (v2_pre_topc @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc6_tops_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(fc1_tex_2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X14)
% 0.21/0.49          | ~ (v1_subset_1 @ X15 @ X14)
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.21/0.49          | ~ (v1_xboole_0 @ (k3_subset_1 @ X14 @ X15)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.21/0.49        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc4_subset_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.49          | ~ (v1_subset_1 @ X4 @ X5)
% 0.21/0.49          | ~ (v1_xboole_0 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))),
% 0.21/0.49      inference('clc', [status(thm)], ['12', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((~ (v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['7', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t24_tdlat_3, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.49         ( ![B:$i]:
% 0.21/0.49           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (v3_tdlat_3 @ X18)
% 0.21/0.49          | ~ (v4_pre_topc @ X19 @ X18)
% 0.21/0.49          | (v3_pre_topc @ X19 @ X18)
% 0.21/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.49          | ~ (l1_pre_topc @ X18)
% 0.21/0.49          | ~ (v2_pre_topc @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.49        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.49        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t47_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.21/0.49             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.49          | (v1_tops_1 @ X20 @ X21)
% 0.21/0.49          | ~ (v3_tex_2 @ X20 @ X21)
% 0.21/0.49          | ~ (v3_pre_topc @ X20 @ X21)
% 0.21/0.49          | ~ (l1_pre_topc @ X21)
% 0.21/0.49          | ~ (v2_pre_topc @ X21)
% 0.21/0.49          | (v2_struct_0 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.49        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.21/0.49        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.49        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.21/0.49  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(d4_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.49             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.49          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 0.21/0.49          | (v2_tops_1 @ X8 @ X9)
% 0.21/0.49          | ~ (l1_pre_topc @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v2_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v1_tops_1 @ 
% 0.21/0.49             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.21/0.49             sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (((v2_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (((v2_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t93_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.21/0.49             ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | (v3_tops_1 @ X12 @ X13)
% 0.21/0.49          | ~ (v4_pre_topc @ X12 @ X13)
% 0.21/0.49          | ~ (v2_tops_1 @ X12 @ X13)
% 0.21/0.49          | ~ (l1_pre_topc @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t93_tops_1])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v2_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | (v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((~ (v2_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | (v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((((v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.21/0.49              sk_A)))
% 0.21/0.49         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '28'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t29_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.49             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10) @ X11)
% 0.21/0.49          | (v4_pre_topc @ X10 @ X11)
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ 
% 0.21/0.49             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.21/0.49             sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['55', '61'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (((v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '62'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['20'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((v2_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (((v2_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      ((~ (v2_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | (v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      ((((v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49         | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.21/0.49              sk_A)))
% 0.21/0.49         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['20'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (((v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['70', '73'])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      ((~ (v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['7', '18'])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.49  thf('78', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('79', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (v3_tdlat_3 @ X18)
% 0.21/0.49          | ~ (v4_pre_topc @ X19 @ X18)
% 0.21/0.49          | (v3_pre_topc @ X19 @ X18)
% 0.21/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.49          | ~ (l1_pre_topc @ X18)
% 0.21/0.49          | ~ (v2_pre_topc @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.49  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('83', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.21/0.49  thf('85', plain,
% 0.21/0.49      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['77', '84'])).
% 0.21/0.49  thf('86', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['76', '85'])).
% 0.21/0.49  thf('87', plain,
% 0.21/0.49      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['20'])).
% 0.21/0.49  thf('88', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.21/0.49  thf('89', plain,
% 0.21/0.49      ((v3_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['63', '88'])).
% 0.21/0.49  thf('90', plain,
% 0.21/0.49      (~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '89'])).
% 0.21/0.49  thf('91', plain,
% 0.21/0.49      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['55', '61'])).
% 0.21/0.49  thf('92', plain,
% 0.21/0.49      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.21/0.49  thf('93', plain,
% 0.21/0.49      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))
% 0.21/0.49         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.49  thf('94', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.21/0.49  thf('95', plain,
% 0.21/0.49      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['93', '94'])).
% 0.21/0.49  thf('96', plain, ($false), inference('demod', [status(thm)], ['90', '95'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
