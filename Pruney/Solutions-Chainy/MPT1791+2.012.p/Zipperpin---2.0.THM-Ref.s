%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sm8yEy5XQI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 497 expanded)
%              Number of leaves         :   33 ( 156 expanded)
%              Depth                    :   31
%              Number of atoms          : 1626 (5533 expanded)
%              Number of equality atoms :   86 ( 292 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t106_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k6_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tmap_1])).

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t103_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
          <=> ( ( u1_pre_topc @ A )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ( ( u1_pre_topc @ X16 )
        = ( k5_tmap_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k9_setfam_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ( ( u1_pre_topc @ X16 )
        = ( k5_tmap_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k6_tmap_1 @ X12 @ X11 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( k5_tmap_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k9_setfam_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k6_tmap_1 @ X12 @ X11 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( k5_tmap_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','34'])).

thf('36',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(rc1_connsp_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X10 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_pre_topc @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k9_setfam_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_pre_topc @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('52',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X10 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(cc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v3_tops_1 @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc3_tops_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k9_setfam_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v3_tops_1 @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( v3_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v3_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v3_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X10 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t97_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( v3_tops_1 @ X8 @ X9 )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t97_tops_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('63',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k9_setfam_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( X8 = o_0_0_xboole_0 )
      | ~ ( v3_tops_1 @ X8 @ X9 )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v3_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v3_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( sk_B @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X10 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ o_0_0_xboole_0 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ o_0_0_xboole_0 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( k5_tmap_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('76',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k9_setfam_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( k5_tmap_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ o_0_0_xboole_0 ) )
        = ( k5_tmap_1 @ X0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ o_0_0_xboole_0 ) )
        = ( k5_tmap_1 @ X0 @ o_0_0_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('80',plain,(
    ! [X3: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf('81',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('82',plain,(
    ! [X3: $i] :
      ( ( r2_hidden @ o_0_0_xboole_0 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ o_0_0_xboole_0 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k9_setfam_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ( ( u1_pre_topc @ X16 )
        = ( k5_tmap_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ o_0_0_xboole_0 ) )
      | ~ ( r2_hidden @ o_0_0_xboole_0 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ o_0_0_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ o_0_0_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ o_0_0_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ o_0_0_xboole_0 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k9_setfam_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k6_tmap_1 @ X12 @ X11 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( k5_tmap_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ o_0_0_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ o_0_0_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ o_0_0_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ o_0_0_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( k6_tmap_1 @ sk_A @ o_0_0_xboole_0 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['93','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k6_tmap_1 @ sk_A @ o_0_0_xboole_0 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k6_tmap_1 @ sk_A @ o_0_0_xboole_0 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('105',plain,
    ( ( ( k6_tmap_1 @ sk_A @ o_0_0_xboole_0 )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('107',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k9_setfam_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( k5_tmap_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ o_0_0_xboole_0 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['105','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t102_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('116',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r2_hidden @ X13 @ ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('118',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r2_hidden @ X13 @ ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    r2_hidden @ sk_B_1 @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ o_0_0_xboole_0 ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['114','124'])).

thf('126',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k5_tmap_1 @ sk_A @ o_0_0_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['78','125'])).

thf('127',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('134',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ( v3_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k9_setfam_1 @ X0 )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('136',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ( v3_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['132','139'])).

thf('141',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sm8yEy5XQI
% 0.13/0.37  % Computer   : n009.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:00:26 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 122 iterations in 0.082s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.56  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.22/0.56  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.56  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.22/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.56  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.22/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.56  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.22/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.56  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.22/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(t106_tmap_1, conjecture,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.56             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.56               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i]:
% 0.22/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.56            ( l1_pre_topc @ A ) ) =>
% 0.22/0.56          ( ![B:$i]:
% 0.22/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56              ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.56                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.56                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56          != (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.22/0.56        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      (~
% 0.22/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.22/0.56       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56          = (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.22/0.56        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['2'])).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(redefinition_k9_setfam_1, axiom,
% 0.22/0.56    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.56  thf('5', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf(d5_pre_topc, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.56             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.22/0.56          | ~ (v3_pre_topc @ X1 @ X2)
% 0.22/0.56          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.22/0.56          | ~ (l1_pre_topc @ X2))),
% 0.22/0.56      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.22/0.56  thf('8', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('9', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ (u1_struct_0 @ X2)))
% 0.22/0.56          | ~ (v3_pre_topc @ X1 @ X2)
% 0.22/0.56          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.22/0.56          | ~ (l1_pre_topc @ X2))),
% 0.22/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.22/0.56        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.56  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.22/0.56        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))
% 0.22/0.56         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['3', '12'])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf(t103_tmap_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.22/0.56             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      (![X15 : $i, X16 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.56          | ~ (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.22/0.56          | ((u1_pre_topc @ X16) = (k5_tmap_1 @ X16 @ X15))
% 0.22/0.56          | ~ (l1_pre_topc @ X16)
% 0.22/0.56          | ~ (v2_pre_topc @ X16)
% 0.22/0.56          | (v2_struct_0 @ X16))),
% 0.22/0.56      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.22/0.56  thf('16', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      (![X15 : $i, X16 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X15 @ (k9_setfam_1 @ (u1_struct_0 @ X16)))
% 0.22/0.56          | ~ (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.22/0.56          | ((u1_pre_topc @ X16) = (k5_tmap_1 @ X16 @ X15))
% 0.22/0.56          | ~ (l1_pre_topc @ X16)
% 0.22/0.56          | ~ (v2_pre_topc @ X16)
% 0.22/0.56          | (v2_struct_0 @ X16))),
% 0.22/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.22/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.56  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.22/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.56  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('23', plain,
% 0.22/0.56      ((~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.22/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1)))
% 0.22/0.56         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['13', '23'])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf(d9_tmap_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( k6_tmap_1 @ A @ B ) =
% 0.22/0.56             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (![X11 : $i, X12 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.56          | ((k6_tmap_1 @ X12 @ X11)
% 0.22/0.56              = (g1_pre_topc @ (u1_struct_0 @ X12) @ (k5_tmap_1 @ X12 @ X11)))
% 0.22/0.56          | ~ (l1_pre_topc @ X12)
% 0.22/0.56          | ~ (v2_pre_topc @ X12)
% 0.22/0.56          | (v2_struct_0 @ X12))),
% 0.22/0.56      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.22/0.56  thf('27', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (![X11 : $i, X12 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X11 @ (k9_setfam_1 @ (u1_struct_0 @ X12)))
% 0.22/0.56          | ((k6_tmap_1 @ X12 @ X11)
% 0.22/0.56              = (g1_pre_topc @ (u1_struct_0 @ X12) @ (k5_tmap_1 @ X12 @ X11)))
% 0.22/0.56          | ~ (l1_pre_topc @ X12)
% 0.22/0.56          | ~ (v2_pre_topc @ X12)
% 0.22/0.56          | (v2_struct_0 @ X12))),
% 0.22/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | ((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.22/0.56            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['25', '28'])).
% 0.22/0.56  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('32', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.22/0.56            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.56  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.22/0.56         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      ((((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.22/0.56          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.22/0.56         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['24', '34'])).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56          != (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.22/0.56         <= (~
% 0.22/0.56             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      ((((k6_tmap_1 @ sk_A @ sk_B_1) != (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.22/0.56         <= (~
% 0.22/0.56             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.22/0.56             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.22/0.56       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.22/0.56       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('split', [status(esa)], ['2'])).
% 0.22/0.56  thf(rc1_connsp_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ?[B:$i]:
% 0.22/0.56         ( ( v1_xboole_0 @ B ) & 
% 0.22/0.56           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      (![X10 : $i]: ((v1_xboole_0 @ (sk_B @ X10)) | ~ (l1_pre_topc @ X10))),
% 0.22/0.56      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      (![X10 : $i]:
% 0.22/0.56         ((m1_subset_1 @ (sk_B @ X10) @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.56          | ~ (l1_pre_topc @ X10))),
% 0.22/0.56      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.22/0.56  thf('42', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('43', plain,
% 0.22/0.56      (![X10 : $i]:
% 0.22/0.56         ((m1_subset_1 @ (sk_B @ X10) @ (k9_setfam_1 @ (u1_struct_0 @ X10)))
% 0.22/0.56          | ~ (l1_pre_topc @ X10))),
% 0.22/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.56  thf(cc1_tops_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      (![X4 : $i, X5 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.22/0.56          | (v3_pre_topc @ X4 @ X5)
% 0.22/0.56          | ~ (v1_xboole_0 @ X4)
% 0.22/0.56          | ~ (l1_pre_topc @ X5)
% 0.22/0.56          | ~ (v2_pre_topc @ X5))),
% 0.22/0.56      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.22/0.56  thf('45', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('46', plain,
% 0.22/0.56      (![X4 : $i, X5 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X4 @ (k9_setfam_1 @ (u1_struct_0 @ X5)))
% 0.22/0.56          | (v3_pre_topc @ X4 @ X5)
% 0.22/0.56          | ~ (v1_xboole_0 @ X4)
% 0.22/0.56          | ~ (l1_pre_topc @ X5)
% 0.22/0.56          | ~ (v2_pre_topc @ X5))),
% 0.22/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.56  thf('47', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v1_xboole_0 @ (sk_B @ X0))
% 0.22/0.56          | (v3_pre_topc @ (sk_B @ X0) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['43', '46'])).
% 0.22/0.56  thf('48', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ~ (v1_xboole_0 @ (sk_B @ X0))
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['47'])).
% 0.22/0.56  thf('49', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | (v3_pre_topc @ (sk_B @ X0) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['40', '48'])).
% 0.22/0.56  thf('50', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.56  thf('51', plain,
% 0.22/0.56      (![X10 : $i]: ((v1_xboole_0 @ (sk_B @ X10)) | ~ (l1_pre_topc @ X10))),
% 0.22/0.56      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.22/0.56  thf('52', plain,
% 0.22/0.56      (![X10 : $i]:
% 0.22/0.56         ((m1_subset_1 @ (sk_B @ X10) @ (k9_setfam_1 @ (u1_struct_0 @ X10)))
% 0.22/0.56          | ~ (l1_pre_topc @ X10))),
% 0.22/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.56  thf(cc3_tops_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( v1_xboole_0 @ B ) => ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.22/0.56  thf('53', plain,
% 0.22/0.56      (![X6 : $i, X7 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.56          | (v3_tops_1 @ X6 @ X7)
% 0.22/0.56          | ~ (v1_xboole_0 @ X6)
% 0.22/0.56          | ~ (l1_pre_topc @ X7)
% 0.22/0.56          | ~ (v2_pre_topc @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [cc3_tops_1])).
% 0.22/0.56  thf('54', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('55', plain,
% 0.22/0.56      (![X6 : $i, X7 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X6 @ (k9_setfam_1 @ (u1_struct_0 @ X7)))
% 0.22/0.56          | (v3_tops_1 @ X6 @ X7)
% 0.22/0.56          | ~ (v1_xboole_0 @ X6)
% 0.22/0.56          | ~ (l1_pre_topc @ X7)
% 0.22/0.56          | ~ (v2_pre_topc @ X7))),
% 0.22/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.22/0.56  thf('56', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v1_xboole_0 @ (sk_B @ X0))
% 0.22/0.56          | (v3_tops_1 @ (sk_B @ X0) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['52', '55'])).
% 0.22/0.56  thf('57', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v3_tops_1 @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ~ (v1_xboole_0 @ (sk_B @ X0))
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.56  thf('58', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | (v3_tops_1 @ (sk_B @ X0) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['51', '57'])).
% 0.22/0.56  thf('59', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v3_tops_1 @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.56  thf('60', plain,
% 0.22/0.56      (![X10 : $i]:
% 0.22/0.56         ((m1_subset_1 @ (sk_B @ X10) @ (k9_setfam_1 @ (u1_struct_0 @ X10)))
% 0.22/0.56          | ~ (l1_pre_topc @ X10))),
% 0.22/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.56  thf(t97_tops_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.22/0.56             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.56  thf('61', plain,
% 0.22/0.56      (![X8 : $i, X9 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.56          | ((X8) = (k1_xboole_0))
% 0.22/0.56          | ~ (v3_tops_1 @ X8 @ X9)
% 0.22/0.56          | ~ (v3_pre_topc @ X8 @ X9)
% 0.22/0.56          | ~ (l1_pre_topc @ X9)
% 0.22/0.56          | ~ (v2_pre_topc @ X9))),
% 0.22/0.56      inference('cnf', [status(esa)], [t97_tops_1])).
% 0.22/0.56  thf('62', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.22/0.56  thf('63', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.56  thf('64', plain,
% 0.22/0.56      (![X8 : $i, X9 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X8 @ (k9_setfam_1 @ (u1_struct_0 @ X9)))
% 0.22/0.56          | ((X8) = (o_0_0_xboole_0))
% 0.22/0.56          | ~ (v3_tops_1 @ X8 @ X9)
% 0.22/0.56          | ~ (v3_pre_topc @ X8 @ X9)
% 0.22/0.56          | ~ (l1_pre_topc @ X9)
% 0.22/0.56          | ~ (v2_pre_topc @ X9))),
% 0.22/0.56      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.22/0.56  thf('65', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ~ (v3_tops_1 @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ((sk_B @ X0) = (o_0_0_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['60', '64'])).
% 0.22/0.56  thf('66', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((sk_B @ X0) = (o_0_0_xboole_0))
% 0.22/0.56          | ~ (v3_tops_1 @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['65'])).
% 0.22/0.56  thf('67', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ((sk_B @ X0) = (o_0_0_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['59', '66'])).
% 0.22/0.56  thf('68', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((sk_B @ X0) = (o_0_0_xboole_0))
% 0.22/0.56          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.22/0.56  thf('69', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ((sk_B @ X0) = (o_0_0_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['50', '68'])).
% 0.22/0.56  thf('70', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((sk_B @ X0) = (o_0_0_xboole_0))
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['69'])).
% 0.22/0.56  thf('71', plain,
% 0.22/0.56      (![X10 : $i]:
% 0.22/0.56         ((m1_subset_1 @ (sk_B @ X10) @ (k9_setfam_1 @ (u1_struct_0 @ X10)))
% 0.22/0.56          | ~ (l1_pre_topc @ X10))),
% 0.22/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.56  thf('72', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((m1_subset_1 @ o_0_0_xboole_0 @ (k9_setfam_1 @ (u1_struct_0 @ X0)))
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['70', '71'])).
% 0.22/0.56  thf('73', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | (m1_subset_1 @ o_0_0_xboole_0 @ (k9_setfam_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['72'])).
% 0.22/0.56  thf(t104_tmap_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.56             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.56  thf('74', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.56          | ((u1_pre_topc @ (k6_tmap_1 @ X18 @ X17)) = (k5_tmap_1 @ X18 @ X17))
% 0.22/0.56          | ~ (l1_pre_topc @ X18)
% 0.22/0.56          | ~ (v2_pre_topc @ X18)
% 0.22/0.56          | (v2_struct_0 @ X18))),
% 0.22/0.56      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.22/0.56  thf('75', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('76', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X17 @ (k9_setfam_1 @ (u1_struct_0 @ X18)))
% 0.22/0.56          | ((u1_pre_topc @ (k6_tmap_1 @ X18 @ X17)) = (k5_tmap_1 @ X18 @ X17))
% 0.22/0.56          | ~ (l1_pre_topc @ X18)
% 0.22/0.56          | ~ (v2_pre_topc @ X18)
% 0.22/0.56          | (v2_struct_0 @ X18))),
% 0.22/0.56      inference('demod', [status(thm)], ['74', '75'])).
% 0.22/0.56  thf('77', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | (v2_struct_0 @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ o_0_0_xboole_0))
% 0.22/0.56              = (k5_tmap_1 @ X0 @ o_0_0_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['73', '76'])).
% 0.22/0.56  thf('78', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((u1_pre_topc @ (k6_tmap_1 @ X0 @ o_0_0_xboole_0))
% 0.22/0.56            = (k5_tmap_1 @ X0 @ o_0_0_xboole_0))
% 0.22/0.56          | (v2_struct_0 @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['77'])).
% 0.22/0.56  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t5_pre_topc, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ))).
% 0.22/0.56  thf('80', plain,
% 0.22/0.56      (![X3 : $i]:
% 0.22/0.56         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X3))
% 0.22/0.56          | ~ (l1_pre_topc @ X3)
% 0.22/0.56          | ~ (v2_pre_topc @ X3))),
% 0.22/0.56      inference('cnf', [status(esa)], [t5_pre_topc])).
% 0.22/0.56  thf('81', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.56  thf('82', plain,
% 0.22/0.56      (![X3 : $i]:
% 0.22/0.56         ((r2_hidden @ o_0_0_xboole_0 @ (u1_pre_topc @ X3))
% 0.22/0.56          | ~ (l1_pre_topc @ X3)
% 0.22/0.56          | ~ (v2_pre_topc @ X3))),
% 0.22/0.56      inference('demod', [status(thm)], ['80', '81'])).
% 0.22/0.56  thf('83', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | (m1_subset_1 @ o_0_0_xboole_0 @ (k9_setfam_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['72'])).
% 0.22/0.56  thf('84', plain,
% 0.22/0.56      (![X15 : $i, X16 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X15 @ (k9_setfam_1 @ (u1_struct_0 @ X16)))
% 0.22/0.56          | ~ (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.22/0.56          | ((u1_pre_topc @ X16) = (k5_tmap_1 @ X16 @ X15))
% 0.22/0.56          | ~ (l1_pre_topc @ X16)
% 0.22/0.56          | ~ (v2_pre_topc @ X16)
% 0.22/0.56          | (v2_struct_0 @ X16))),
% 0.22/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.56  thf('85', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | (v2_struct_0 @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ o_0_0_xboole_0))
% 0.22/0.56          | ~ (r2_hidden @ o_0_0_xboole_0 @ (u1_pre_topc @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.22/0.56  thf('86', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (r2_hidden @ o_0_0_xboole_0 @ (u1_pre_topc @ X0))
% 0.22/0.56          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ o_0_0_xboole_0))
% 0.22/0.56          | (v2_struct_0 @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['85'])).
% 0.22/0.56  thf('87', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | (v2_struct_0 @ X0)
% 0.22/0.56          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ o_0_0_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['82', '86'])).
% 0.22/0.56  thf('88', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ o_0_0_xboole_0))
% 0.22/0.56          | (v2_struct_0 @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['87'])).
% 0.22/0.56  thf('89', plain,
% 0.22/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ o_0_0_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['79', '88'])).
% 0.22/0.56  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('91', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ o_0_0_xboole_0)))),
% 0.22/0.56      inference('demod', [status(thm)], ['89', '90'])).
% 0.22/0.56  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('93', plain,
% 0.22/0.56      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ o_0_0_xboole_0))),
% 0.22/0.56      inference('clc', [status(thm)], ['91', '92'])).
% 0.22/0.56  thf('94', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | (m1_subset_1 @ o_0_0_xboole_0 @ (k9_setfam_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['72'])).
% 0.22/0.56  thf('95', plain,
% 0.22/0.56      (![X11 : $i, X12 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X11 @ (k9_setfam_1 @ (u1_struct_0 @ X12)))
% 0.22/0.56          | ((k6_tmap_1 @ X12 @ X11)
% 0.22/0.56              = (g1_pre_topc @ (u1_struct_0 @ X12) @ (k5_tmap_1 @ X12 @ X11)))
% 0.22/0.56          | ~ (l1_pre_topc @ X12)
% 0.22/0.56          | ~ (v2_pre_topc @ X12)
% 0.22/0.56          | (v2_struct_0 @ X12))),
% 0.22/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.56  thf('96', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | (v2_struct_0 @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | ((k6_tmap_1 @ X0 @ o_0_0_xboole_0)
% 0.22/0.56              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.22/0.56                 (k5_tmap_1 @ X0 @ o_0_0_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.22/0.56  thf('97', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k6_tmap_1 @ X0 @ o_0_0_xboole_0)
% 0.22/0.56            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.22/0.56               (k5_tmap_1 @ X0 @ o_0_0_xboole_0)))
% 0.22/0.56          | (v2_struct_0 @ X0)
% 0.22/0.56          | ~ (v2_pre_topc @ X0)
% 0.22/0.56          | ~ (l1_pre_topc @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['96'])).
% 0.22/0.56  thf('98', plain,
% 0.22/0.56      ((((k6_tmap_1 @ sk_A @ o_0_0_xboole_0)
% 0.22/0.56          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('sup+', [status(thm)], ['93', '97'])).
% 0.22/0.56  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('101', plain,
% 0.22/0.56      ((((k6_tmap_1 @ sk_A @ o_0_0_xboole_0)
% 0.22/0.56          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.56        | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.22/0.56  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('103', plain,
% 0.22/0.56      (((k6_tmap_1 @ sk_A @ o_0_0_xboole_0)
% 0.22/0.56         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.22/0.56      inference('clc', [status(thm)], ['101', '102'])).
% 0.22/0.56  thf('104', plain,
% 0.22/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56          = (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.22/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('split', [status(esa)], ['2'])).
% 0.22/0.56  thf('105', plain,
% 0.22/0.56      ((((k6_tmap_1 @ sk_A @ o_0_0_xboole_0) = (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.22/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('sup+', [status(thm)], ['103', '104'])).
% 0.22/0.56  thf('106', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf('107', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X17 @ (k9_setfam_1 @ (u1_struct_0 @ X18)))
% 0.22/0.56          | ((u1_pre_topc @ (k6_tmap_1 @ X18 @ X17)) = (k5_tmap_1 @ X18 @ X17))
% 0.22/0.56          | ~ (l1_pre_topc @ X18)
% 0.22/0.56          | ~ (v2_pre_topc @ X18)
% 0.22/0.56          | (v2_struct_0 @ X18))),
% 0.22/0.56      inference('demod', [status(thm)], ['74', '75'])).
% 0.22/0.56  thf('108', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.22/0.56            = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['106', '107'])).
% 0.22/0.56  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('111', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.22/0.56            = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.22/0.56  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('113', plain,
% 0.22/0.56      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.22/0.56         = (k5_tmap_1 @ sk_A @ sk_B_1))),
% 0.22/0.56      inference('clc', [status(thm)], ['111', '112'])).
% 0.22/0.56  thf('114', plain,
% 0.22/0.56      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ o_0_0_xboole_0))
% 0.22/0.56          = (k5_tmap_1 @ sk_A @ sk_B_1)))
% 0.22/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('sup+', [status(thm)], ['105', '113'])).
% 0.22/0.56  thf('115', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf(t102_tmap_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.22/0.56  thf('116', plain,
% 0.22/0.56      (![X13 : $i, X14 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.56          | (r2_hidden @ X13 @ (k5_tmap_1 @ X14 @ X13))
% 0.22/0.56          | ~ (l1_pre_topc @ X14)
% 0.22/0.56          | ~ (v2_pre_topc @ X14)
% 0.22/0.56          | (v2_struct_0 @ X14))),
% 0.22/0.56      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.22/0.56  thf('117', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('118', plain,
% 0.22/0.56      (![X13 : $i, X14 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X13 @ (k9_setfam_1 @ (u1_struct_0 @ X14)))
% 0.22/0.56          | (r2_hidden @ X13 @ (k5_tmap_1 @ X14 @ X13))
% 0.22/0.56          | ~ (l1_pre_topc @ X14)
% 0.22/0.56          | ~ (v2_pre_topc @ X14)
% 0.22/0.56          | (v2_struct_0 @ X14))),
% 0.22/0.56      inference('demod', [status(thm)], ['116', '117'])).
% 0.22/0.56  thf('119', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (r2_hidden @ sk_B_1 @ (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['115', '118'])).
% 0.22/0.56  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('122', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | (r2_hidden @ sk_B_1 @ (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.22/0.56  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('124', plain, ((r2_hidden @ sk_B_1 @ (k5_tmap_1 @ sk_A @ sk_B_1))),
% 0.22/0.56      inference('clc', [status(thm)], ['122', '123'])).
% 0.22/0.56  thf('125', plain,
% 0.22/0.56      (((r2_hidden @ sk_B_1 @ 
% 0.22/0.56         (u1_pre_topc @ (k6_tmap_1 @ sk_A @ o_0_0_xboole_0))))
% 0.22/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('sup+', [status(thm)], ['114', '124'])).
% 0.22/0.56  thf('126', plain,
% 0.22/0.56      ((((r2_hidden @ sk_B_1 @ (k5_tmap_1 @ sk_A @ o_0_0_xboole_0))
% 0.22/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.22/0.56         | (v2_struct_0 @ sk_A)))
% 0.22/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('sup+', [status(thm)], ['78', '125'])).
% 0.22/0.56  thf('127', plain,
% 0.22/0.56      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ o_0_0_xboole_0))),
% 0.22/0.56      inference('clc', [status(thm)], ['91', '92'])).
% 0.22/0.56  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('130', plain,
% 0.22/0.56      ((((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.22/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.22/0.56  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('132', plain,
% 0.22/0.56      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))
% 0.22/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('clc', [status(thm)], ['130', '131'])).
% 0.22/0.56  thf('133', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf('134', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.22/0.56          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.22/0.56          | (v3_pre_topc @ X1 @ X2)
% 0.22/0.56          | ~ (l1_pre_topc @ X2))),
% 0.22/0.56      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.22/0.56  thf('135', plain, (![X0 : $i]: ((k9_setfam_1 @ X0) = (k1_zfmisc_1 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.56  thf('136', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ (u1_struct_0 @ X2)))
% 0.22/0.56          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.22/0.56          | (v3_pre_topc @ X1 @ X2)
% 0.22/0.56          | ~ (l1_pre_topc @ X2))),
% 0.22/0.56      inference('demod', [status(thm)], ['134', '135'])).
% 0.22/0.56  thf('137', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['133', '136'])).
% 0.22/0.56  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('139', plain,
% 0.22/0.56      (((v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['137', '138'])).
% 0.22/0.56  thf('140', plain,
% 0.22/0.56      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 0.22/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['132', '139'])).
% 0.22/0.56  thf('141', plain,
% 0.22/0.56      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('142', plain,
% 0.22/0.56      (~
% 0.22/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.56          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.22/0.56       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['140', '141'])).
% 0.22/0.56  thf('143', plain, ($false),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '142'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
