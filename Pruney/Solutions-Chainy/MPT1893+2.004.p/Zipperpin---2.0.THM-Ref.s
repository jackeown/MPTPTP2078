%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y0RR9l8Xei

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 592 expanded)
%              Number of leaves         :   38 ( 194 expanded)
%              Depth                    :   19
%              Number of atoms          : 1197 (6694 expanded)
%              Number of equality atoms :   58 ( 187 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_subset_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tex_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v1_tops_1 @ X27 @ X28 )
      | ~ ( v3_tex_2 @ X27 @ X28 )
      | ~ ( v3_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_tdlat_3 @ X25 )
      | ~ ( v4_pre_topc @ X26 @ X25 )
      | ( v3_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('47',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('49',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('51',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('52',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['7','12'])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','83'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','84','85'])).

thf('87',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('88',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['36','88'])).

thf('90',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('92',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('96',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('99',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('101',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('103',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('110',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['101','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('113',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['110','117'])).

thf('119',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('120',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('121',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['118','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('125',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_tdlat_3 @ X25 )
      | ~ ( v4_pre_topc @ X26 @ X25 )
      | ( v3_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( v3_tdlat_3 @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['96','131'])).

thf('133',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['90','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','83'])).

thf('135',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['13','133','134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y0RR9l8Xei
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.61  % Solved by: fo/fo7.sh
% 0.21/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.61  % done 648 iterations in 0.180s
% 0.21/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.61  % SZS output start Refutation
% 0.21/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.61  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.61  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.61  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.61  thf(t61_tex_2, conjecture,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.61         ( l1_pre_topc @ A ) ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.61           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.61                ( v3_tex_2 @ B @ A ) & 
% 0.21/0.61                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.61    (~( ![A:$i]:
% 0.21/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.61            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.61          ( ![B:$i]:
% 0.21/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.61              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.61                   ( v3_tex_2 @ B @ A ) & 
% 0.21/0.61                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.61    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.21/0.61  thf('0', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(fc1_tex_2, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.21/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.61       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.21/0.61  thf('1', plain,
% 0.21/0.61      (![X23 : $i, X24 : $i]:
% 0.21/0.61         ((v1_xboole_0 @ X23)
% 0.21/0.61          | ~ (v1_subset_1 @ X24 @ X23)
% 0.21/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.21/0.61          | ~ (v1_xboole_0 @ (k3_subset_1 @ X23 @ X24)))),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.21/0.61  thf('2', plain,
% 0.21/0.61      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.61        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.61  thf('3', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(d5_subset_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.61  thf('4', plain,
% 0.21/0.61      (![X8 : $i, X9 : $i]:
% 0.21/0.61         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.21/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.61  thf('5', plain,
% 0.21/0.61      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.21/0.61         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.21/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.61  thf('6', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('7', plain,
% 0.21/0.61      ((~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.21/0.61  thf('8', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(cc4_subset_1, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.61           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.61  thf('9', plain,
% 0.21/0.61      (![X12 : $i, X13 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.61          | ~ (v1_subset_1 @ X12 @ X13)
% 0.21/0.61          | ~ (v1_xboole_0 @ X13))),
% 0.21/0.61      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.21/0.61  thf('10', plain,
% 0.21/0.61      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.61  thf('11', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('12', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.61  thf('13', plain,
% 0.21/0.61      (~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.21/0.61      inference('clc', [status(thm)], ['7', '12'])).
% 0.21/0.61  thf('14', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(t52_pre_topc, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( l1_pre_topc @ A ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.61  thf('15', plain,
% 0.21/0.61      (![X17 : $i, X18 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.61          | ~ (v4_pre_topc @ X17 @ X18)
% 0.21/0.61          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.21/0.61          | ~ (l1_pre_topc @ X18))),
% 0.21/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.61  thf('16', plain,
% 0.21/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.61        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.21/0.61        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.61  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('18', plain,
% 0.21/0.61      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.21/0.61        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.61  thf('19', plain,
% 0.21/0.61      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('20', plain,
% 0.21/0.61      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('split', [status(esa)], ['19'])).
% 0.21/0.61  thf('21', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(t47_tex_2, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.61           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.21/0.61             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.61  thf('22', plain,
% 0.21/0.61      (![X27 : $i, X28 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.61          | (v1_tops_1 @ X27 @ X28)
% 0.21/0.61          | ~ (v3_tex_2 @ X27 @ X28)
% 0.21/0.61          | ~ (v3_pre_topc @ X27 @ X28)
% 0.21/0.61          | ~ (l1_pre_topc @ X28)
% 0.21/0.61          | ~ (v2_pre_topc @ X28)
% 0.21/0.61          | (v2_struct_0 @ X28))),
% 0.21/0.61      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.21/0.61  thf('23', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.61        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.61        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.61        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.61  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('26', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('27', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.61        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.21/0.61  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('29', plain,
% 0.21/0.61      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.61  thf('30', plain,
% 0.21/0.61      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['20', '29'])).
% 0.21/0.61  thf('31', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(d2_tops_3, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( l1_pre_topc @ A ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.61           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.61             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.61  thf('32', plain,
% 0.21/0.61      (![X21 : $i, X22 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.61          | ~ (v1_tops_1 @ X21 @ X22)
% 0.21/0.61          | ((k2_pre_topc @ X22 @ X21) = (u1_struct_0 @ X22))
% 0.21/0.61          | ~ (l1_pre_topc @ X22))),
% 0.21/0.61      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.61  thf('33', plain,
% 0.21/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.61        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.61        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.61  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('35', plain,
% 0.21/0.61      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.61        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.61  thf('36', plain,
% 0.21/0.61      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.21/0.61         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['30', '35'])).
% 0.21/0.61  thf('37', plain,
% 0.21/0.61      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('split', [status(esa)], ['19'])).
% 0.21/0.61  thf('38', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(t24_tdlat_3, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.61       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.61         ( ![B:$i]:
% 0.21/0.61           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.61             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.61  thf('39', plain,
% 0.21/0.61      (![X25 : $i, X26 : $i]:
% 0.21/0.61         (~ (v3_tdlat_3 @ X25)
% 0.21/0.61          | ~ (v4_pre_topc @ X26 @ X25)
% 0.21/0.61          | (v3_pre_topc @ X26 @ X25)
% 0.21/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.61          | ~ (l1_pre_topc @ X25)
% 0.21/0.61          | ~ (v2_pre_topc @ X25))),
% 0.21/0.61      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.21/0.61  thf('40', plain,
% 0.21/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.61        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.61        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.61        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.61  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('43', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('44', plain,
% 0.21/0.61      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.21/0.61  thf('45', plain,
% 0.21/0.61      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['37', '44'])).
% 0.21/0.61  thf('46', plain,
% 0.21/0.61      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.61  thf('47', plain,
% 0.21/0.61      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.61  thf('48', plain,
% 0.21/0.61      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.61        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.61  thf('49', plain,
% 0.21/0.61      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.21/0.61         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.61  thf('50', plain,
% 0.21/0.61      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('split', [status(esa)], ['19'])).
% 0.21/0.61  thf('51', plain,
% 0.21/0.61      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.21/0.61        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.61  thf('52', plain,
% 0.21/0.61      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.21/0.61         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.61  thf('53', plain,
% 0.21/0.61      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('sup+', [status(thm)], ['49', '52'])).
% 0.21/0.61  thf('54', plain,
% 0.21/0.61      (~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.21/0.61      inference('clc', [status(thm)], ['7', '12'])).
% 0.21/0.61  thf('55', plain,
% 0.21/0.61      ((~ (v1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.21/0.61         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.61  thf(t48_xboole_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.61  thf('56', plain,
% 0.21/0.61      (![X6 : $i, X7 : $i]:
% 0.21/0.61         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.61           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.61  thf(t36_xboole_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.61  thf('57', plain,
% 0.21/0.61      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.61  thf(t3_xboole_1, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.61  thf('58', plain,
% 0.21/0.61      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.21/0.61      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.61  thf('59', plain,
% 0.21/0.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.61  thf('60', plain,
% 0.21/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['56', '59'])).
% 0.21/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.61  thf('61', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.61  thf('62', plain,
% 0.21/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.61  thf('63', plain,
% 0.21/0.61      (![X6 : $i, X7 : $i]:
% 0.21/0.61         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.61           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.61  thf('64', plain,
% 0.21/0.61      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.61  thf('65', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.21/0.61      inference('sup+', [status(thm)], ['63', '64'])).
% 0.21/0.61  thf('66', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.61      inference('sup+', [status(thm)], ['62', '65'])).
% 0.21/0.61  thf(t3_subset, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.61  thf('67', plain,
% 0.21/0.61      (![X14 : $i, X16 : $i]:
% 0.21/0.61         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.21/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.61  thf('68', plain,
% 0.21/0.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.61  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.61  thf('69', plain,
% 0.21/0.61      (![X10 : $i, X11 : $i]:
% 0.21/0.61         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.21/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.61  thf('70', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.61  thf('71', plain,
% 0.21/0.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.61  thf('72', plain,
% 0.21/0.61      (![X8 : $i, X9 : $i]:
% 0.21/0.61         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.21/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.61  thf('73', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.61  thf(t3_boole, axiom,
% 0.21/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.61  thf('74', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.61  thf('75', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.61      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.61  thf('76', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.61      inference('demod', [status(thm)], ['70', '75'])).
% 0.21/0.61  thf('77', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.61  thf('78', plain,
% 0.21/0.61      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.61  thf('79', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.61      inference('sup+', [status(thm)], ['77', '78'])).
% 0.21/0.61  thf('80', plain,
% 0.21/0.61      (![X14 : $i, X16 : $i]:
% 0.21/0.61         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.21/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.61  thf('81', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.61  thf('82', plain,
% 0.21/0.61      (![X8 : $i, X9 : $i]:
% 0.21/0.61         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.21/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.61  thf('83', plain,
% 0.21/0.61      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.61  thf('84', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['76', '83'])).
% 0.21/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.61  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('86', plain, (~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['55', '84', '85'])).
% 0.21/0.61  thf('87', plain,
% 0.21/0.61      (((v3_pre_topc @ sk_B_1 @ sk_A)) | ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('split', [status(esa)], ['19'])).
% 0.21/0.61  thf('88', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.21/0.61  thf('89', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.61      inference('simpl_trail', [status(thm)], ['36', '88'])).
% 0.21/0.61  thf('90', plain,
% 0.21/0.61      ((((u1_struct_0 @ sk_A) = (sk_B_1)) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['18', '89'])).
% 0.21/0.61  thf('91', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(t29_tops_1, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( l1_pre_topc @ A ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.61           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.61             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.61  thf('92', plain,
% 0.21/0.61      (![X19 : $i, X20 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.61          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.21/0.61          | (v4_pre_topc @ X19 @ X20)
% 0.21/0.61          | ~ (l1_pre_topc @ X20))),
% 0.21/0.61      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.21/0.61  thf('93', plain,
% 0.21/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.61        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.61        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.61  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('95', plain,
% 0.21/0.61      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.21/0.61         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.21/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.61  thf('96', plain,
% 0.21/0.61      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.61        | ~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.21/0.61  thf('97', plain,
% 0.21/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('98', plain,
% 0.21/0.61      (![X10 : $i, X11 : $i]:
% 0.21/0.61         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.21/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.61  thf('99', plain,
% 0.21/0.61      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.21/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.61  thf('100', plain,
% 0.21/0.61      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.21/0.61         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.21/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.61  thf('101', plain,
% 0.21/0.61      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.21/0.61      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.61  thf('102', plain,
% 0.21/0.61      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.61  thf('103', plain,
% 0.21/0.61      (![X14 : $i, X16 : $i]:
% 0.21/0.61         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.21/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.61  thf('104', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.61  thf('105', plain,
% 0.21/0.61      (![X8 : $i, X9 : $i]:
% 0.21/0.61         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.21/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.61  thf('106', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.61           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.61  thf('107', plain,
% 0.21/0.61      (![X6 : $i, X7 : $i]:
% 0.21/0.61         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.61           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.61  thf('108', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.61           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.61      inference('demod', [status(thm)], ['106', '107'])).
% 0.21/0.61  thf('109', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.61  thf('110', plain,
% 0.21/0.61      (((k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B_1))),
% 0.21/0.61      inference('demod', [status(thm)], ['101', '108', '109'])).
% 0.21/0.61  thf('111', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.61  thf('112', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.61  thf('113', plain,
% 0.21/0.61      (![X19 : $i, X20 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.61          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.21/0.61          | (v4_pre_topc @ X19 @ X20)
% 0.21/0.61          | ~ (l1_pre_topc @ X20))),
% 0.21/0.61      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.21/0.61  thf('114', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (~ (l1_pre_topc @ X0)
% 0.21/0.61          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.21/0.61          | ~ (v3_pre_topc @ 
% 0.21/0.61               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.61                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.21/0.61               X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.61  thf('115', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.61           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.61      inference('demod', [status(thm)], ['106', '107'])).
% 0.21/0.61  thf('116', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (~ (l1_pre_topc @ X0)
% 0.21/0.61          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.21/0.61          | ~ (v3_pre_topc @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.21/0.61      inference('demod', [status(thm)], ['114', '115'])).
% 0.21/0.61  thf('117', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (~ (v3_pre_topc @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 0.21/0.61          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.21/0.61          | ~ (l1_pre_topc @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['111', '116'])).
% 0.21/0.61  thf('118', plain,
% 0.21/0.61      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.61        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['110', '117'])).
% 0.21/0.61  thf('119', plain,
% 0.21/0.61      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.21/0.61      inference('split', [status(esa)], ['19'])).
% 0.21/0.61  thf('120', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.61      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.21/0.61  thf('121', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.61      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 0.21/0.61  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('123', plain,
% 0.21/0.61      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.21/0.61      inference('demod', [status(thm)], ['118', '121', '122'])).
% 0.21/0.61  thf('124', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.61  thf('125', plain,
% 0.21/0.61      (![X25 : $i, X26 : $i]:
% 0.21/0.61         (~ (v3_tdlat_3 @ X25)
% 0.21/0.61          | ~ (v4_pre_topc @ X26 @ X25)
% 0.21/0.61          | (v3_pre_topc @ X26 @ X25)
% 0.21/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.61          | ~ (l1_pre_topc @ X25)
% 0.21/0.61          | ~ (v2_pre_topc @ X25))),
% 0.21/0.61      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.21/0.61  thf('126', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (~ (v2_pre_topc @ X0)
% 0.21/0.61          | ~ (l1_pre_topc @ X0)
% 0.21/0.61          | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.21/0.61          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.21/0.61          | ~ (v3_tdlat_3 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['124', '125'])).
% 0.21/0.61  thf('127', plain,
% 0.21/0.61      ((~ (v3_tdlat_3 @ sk_A)
% 0.21/0.61        | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.61        | ~ (v2_pre_topc @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['123', '126'])).
% 0.21/0.61  thf('128', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('131', plain,
% 0.21/0.61      ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.21/0.61      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.21/0.61  thf('132', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.61      inference('demod', [status(thm)], ['96', '131'])).
% 0.21/0.61  thf('133', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.21/0.61      inference('demod', [status(thm)], ['90', '132'])).
% 0.21/0.61  thf('134', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.61      inference('sup+', [status(thm)], ['76', '83'])).
% 0.21/0.61  thf('135', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.61  thf('136', plain, ($false),
% 0.21/0.61      inference('demod', [status(thm)], ['13', '133', '134', '135'])).
% 0.21/0.61  
% 0.21/0.61  % SZS output end Refutation
% 0.21/0.61  
% 0.45/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
