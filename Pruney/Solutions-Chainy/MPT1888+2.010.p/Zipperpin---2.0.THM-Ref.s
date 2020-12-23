%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MJ4GaN6DYo

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:29 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 141 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :   21
%              Number of atoms          : 1258 (2797 expanded)
%              Number of equality atoms :   16 (  49 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t56_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                | ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                  = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                  | ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                    = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( m1_subset_1 @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t55_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
               => ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                  = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X18 ) ) )
      | ( ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
        = ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( v3_tdlat_3 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( sk_C @ X2 @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) ) )
        = ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X2 @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( m1_subset_1 @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X18 ) ) )
      | ( ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
        = ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( v3_tdlat_3 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( sk_C @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) @ X2 ) ) )
        = ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) @ X2 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('67',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MJ4GaN6DYo
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:34:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.13/1.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.13/1.35  % Solved by: fo/fo7.sh
% 1.13/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.35  % done 874 iterations in 0.887s
% 1.13/1.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.13/1.35  % SZS output start Refutation
% 1.13/1.35  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.13/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.35  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.13/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.35  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.13/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.35  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.13/1.35  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.13/1.35  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.13/1.35  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.13/1.35  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.13/1.35  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.13/1.35  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 1.13/1.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.13/1.35  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.13/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.35  thf(t56_tex_2, conjecture,
% 1.13/1.35    (![A:$i]:
% 1.13/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.13/1.35         ( l1_pre_topc @ A ) ) =>
% 1.13/1.35       ( ![B:$i]:
% 1.13/1.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.35           ( ![C:$i]:
% 1.13/1.35             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.35               ( ( r1_xboole_0 @
% 1.13/1.35                   ( k2_pre_topc @
% 1.13/1.35                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 1.13/1.35                   ( k2_pre_topc @
% 1.13/1.35                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 1.13/1.35                 ( ( k2_pre_topc @
% 1.13/1.35                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 1.13/1.35                   ( k2_pre_topc @
% 1.13/1.35                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 1.13/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.35    (~( ![A:$i]:
% 1.13/1.35        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.13/1.35            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.35          ( ![B:$i]:
% 1.13/1.35            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.35              ( ![C:$i]:
% 1.13/1.35                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.35                  ( ( r1_xboole_0 @
% 1.13/1.35                      ( k2_pre_topc @
% 1.13/1.35                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 1.13/1.35                      ( k2_pre_topc @
% 1.13/1.35                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 1.13/1.35                    ( ( k2_pre_topc @
% 1.13/1.35                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 1.13/1.35                      ( k2_pre_topc @
% 1.13/1.35                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 1.13/1.35    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 1.13/1.35  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(t3_xboole_0, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.13/1.35            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.13/1.35       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.13/1.35            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.13/1.35  thf('1', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.13/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.13/1.35  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(dt_k6_domain_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.13/1.35       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.13/1.35  thf('3', plain,
% 1.13/1.35      (![X14 : $i, X15 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ X14)
% 1.13/1.35          | ~ (m1_subset_1 @ X15 @ X14)
% 1.13/1.35          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 1.13/1.35      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.13/1.35  thf('4', plain,
% 1.13/1.35      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 1.13/1.35         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.13/1.35        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['2', '3'])).
% 1.13/1.35  thf(dt_k2_pre_topc, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( ( l1_pre_topc @ A ) & 
% 1.13/1.35         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.35       ( m1_subset_1 @
% 1.13/1.35         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.13/1.35  thf('5', plain,
% 1.13/1.35      (![X10 : $i, X11 : $i]:
% 1.13/1.35         (~ (l1_pre_topc @ X10)
% 1.13/1.35          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.13/1.35          | (m1_subset_1 @ (k2_pre_topc @ X10 @ X11) @ 
% 1.13/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 1.13/1.35      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.13/1.35  thf('6', plain,
% 1.13/1.35      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | (m1_subset_1 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.13/1.35        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.35      inference('sup-', [status(thm)], ['4', '5'])).
% 1.13/1.35  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('8', plain,
% 1.13/1.35      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | (m1_subset_1 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.13/1.35      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.35  thf(l3_subset_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.13/1.35       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.13/1.35  thf('9', plain,
% 1.13/1.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X7 @ X8)
% 1.13/1.35          | (r2_hidden @ X7 @ X9)
% 1.13/1.35          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.13/1.35      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.13/1.35  thf('10', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | ~ (r2_hidden @ X0 @ 
% 1.13/1.35               (k2_pre_topc @ sk_A @ 
% 1.13/1.35                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.35  thf('11', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35           X0)
% 1.13/1.35          | (r2_hidden @ 
% 1.13/1.35             (sk_C @ X0 @ 
% 1.13/1.35              (k2_pre_topc @ sk_A @ 
% 1.13/1.35               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))) @ 
% 1.13/1.35             (u1_struct_0 @ sk_A))
% 1.13/1.35          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['1', '10'])).
% 1.13/1.35  thf(d2_subset_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( ( v1_xboole_0 @ A ) =>
% 1.13/1.35         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.13/1.35       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.13/1.35         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.13/1.35  thf('12', plain,
% 1.13/1.35      (![X4 : $i, X5 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X4 @ X5)
% 1.13/1.35          | (m1_subset_1 @ X4 @ X5)
% 1.13/1.35          | (v1_xboole_0 @ X5))),
% 1.13/1.35      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.13/1.35  thf('13', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r1_xboole_0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35             X0)
% 1.13/1.35          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (m1_subset_1 @ 
% 1.13/1.35             (sk_C @ X0 @ 
% 1.13/1.35              (k2_pre_topc @ sk_A @ 
% 1.13/1.35               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))) @ 
% 1.13/1.35             (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['11', '12'])).
% 1.13/1.35  thf('14', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((m1_subset_1 @ 
% 1.13/1.35           (sk_C @ X0 @ 
% 1.13/1.35            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))) @ 
% 1.13/1.35           (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r1_xboole_0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35             X0)
% 1.13/1.35          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['13'])).
% 1.13/1.35  thf('15', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.13/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.13/1.35  thf(t55_tex_2, axiom,
% 1.13/1.35    (![A:$i]:
% 1.13/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.13/1.35         ( l1_pre_topc @ A ) ) =>
% 1.13/1.35       ( ![B:$i]:
% 1.13/1.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.35           ( ![C:$i]:
% 1.13/1.35             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.35               ( ( r2_hidden @
% 1.13/1.35                   B @ 
% 1.13/1.35                   ( k2_pre_topc @
% 1.13/1.35                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 1.13/1.35                 ( ( k2_pre_topc @
% 1.13/1.35                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 1.13/1.35                   ( k2_pre_topc @
% 1.13/1.35                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 1.13/1.35  thf('16', plain,
% 1.13/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 1.13/1.35          | ~ (r2_hidden @ X16 @ 
% 1.13/1.35               (k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X18)))
% 1.13/1.35          | ((k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X16))
% 1.13/1.35              = (k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X18)))
% 1.13/1.35          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 1.13/1.35          | ~ (l1_pre_topc @ X17)
% 1.13/1.35          | ~ (v3_tdlat_3 @ X17)
% 1.13/1.35          | ~ (v2_pre_topc @ X17)
% 1.13/1.35          | (v2_struct_0 @ X17))),
% 1.13/1.35      inference('cnf', [status(esa)], [t55_tex_2])).
% 1.13/1.35  thf('17', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ 
% 1.13/1.35           (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)) @ X2)
% 1.13/1.35          | (v2_struct_0 @ X1)
% 1.13/1.35          | ~ (v2_pre_topc @ X1)
% 1.13/1.35          | ~ (v3_tdlat_3 @ X1)
% 1.13/1.35          | ~ (l1_pre_topc @ X1)
% 1.13/1.35          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.13/1.35          | ((k2_pre_topc @ X1 @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ X1) @ 
% 1.13/1.35               (sk_C @ X2 @ 
% 1.13/1.35                (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)))))
% 1.13/1.35              = (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)))
% 1.13/1.35          | ~ (m1_subset_1 @ 
% 1.13/1.35               (sk_C @ X2 @ 
% 1.13/1.35                (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0))) @ 
% 1.13/1.35               (u1_struct_0 @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['15', '16'])).
% 1.13/1.35  thf('18', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r1_xboole_0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35             X0)
% 1.13/1.35          | ((k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.35               (sk_C @ X0 @ 
% 1.13/1.35                (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))
% 1.13/1.35              = (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 1.13/1.35          | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | ~ (l1_pre_topc @ sk_A)
% 1.13/1.35          | ~ (v3_tdlat_3 @ sk_A)
% 1.13/1.35          | ~ (v2_pre_topc @ sk_A)
% 1.13/1.35          | (v2_struct_0 @ sk_A)
% 1.13/1.35          | (r1_xboole_0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35             X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['14', '17'])).
% 1.13/1.35  thf('19', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('21', plain, ((v3_tdlat_3 @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('23', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r1_xboole_0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35             X0)
% 1.13/1.35          | ((k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.35               (sk_C @ X0 @ 
% 1.13/1.35                (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))
% 1.13/1.35              = (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 1.13/1.35          | (v2_struct_0 @ sk_A)
% 1.13/1.35          | (r1_xboole_0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35             X0))),
% 1.13/1.35      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 1.13/1.35  thf('24', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v2_struct_0 @ sk_A)
% 1.13/1.35          | ((k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.35               (sk_C @ X0 @ 
% 1.13/1.35                (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))
% 1.13/1.35              = (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 1.13/1.35          | (r1_xboole_0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35             X0)
% 1.13/1.35          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['23'])).
% 1.13/1.35  thf('25', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.13/1.35  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('27', plain,
% 1.13/1.35      (![X14 : $i, X15 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ X14)
% 1.13/1.35          | ~ (m1_subset_1 @ X15 @ X14)
% 1.13/1.35          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 1.13/1.35      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.13/1.35  thf('28', plain,
% 1.13/1.35      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.13/1.35         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.13/1.35        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['26', '27'])).
% 1.13/1.35  thf('29', plain,
% 1.13/1.35      (![X10 : $i, X11 : $i]:
% 1.13/1.35         (~ (l1_pre_topc @ X10)
% 1.13/1.35          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.13/1.35          | (m1_subset_1 @ (k2_pre_topc @ X10 @ X11) @ 
% 1.13/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 1.13/1.35      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.13/1.35  thf('30', plain,
% 1.13/1.35      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | (m1_subset_1 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.13/1.35        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.35      inference('sup-', [status(thm)], ['28', '29'])).
% 1.13/1.35  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('32', plain,
% 1.13/1.35      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | (m1_subset_1 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.13/1.35      inference('demod', [status(thm)], ['30', '31'])).
% 1.13/1.35  thf('33', plain,
% 1.13/1.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X7 @ X8)
% 1.13/1.35          | (r2_hidden @ X7 @ X9)
% 1.13/1.35          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.13/1.35      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.13/1.35  thf('34', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | ~ (r2_hidden @ X0 @ 
% 1.13/1.35               (k2_pre_topc @ sk_A @ 
% 1.13/1.35                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['32', '33'])).
% 1.13/1.35  thf('35', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X0 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | (r2_hidden @ 
% 1.13/1.35             (sk_C @ 
% 1.13/1.35              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35              X0) @ 
% 1.13/1.35             (u1_struct_0 @ sk_A))
% 1.13/1.35          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['25', '34'])).
% 1.13/1.35  thf('36', plain,
% 1.13/1.35      (![X4 : $i, X5 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X4 @ X5)
% 1.13/1.35          | (m1_subset_1 @ X4 @ X5)
% 1.13/1.35          | (v1_xboole_0 @ X5))),
% 1.13/1.35      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.13/1.35  thf('37', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r1_xboole_0 @ X0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (m1_subset_1 @ 
% 1.13/1.35             (sk_C @ 
% 1.13/1.35              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35              X0) @ 
% 1.13/1.35             (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['35', '36'])).
% 1.13/1.35  thf('38', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((m1_subset_1 @ 
% 1.13/1.35           (sk_C @ 
% 1.13/1.35            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35            X0) @ 
% 1.13/1.35           (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r1_xboole_0 @ X0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['37'])).
% 1.13/1.35  thf('39', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.13/1.35  thf('40', plain,
% 1.13/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 1.13/1.35          | ~ (r2_hidden @ X16 @ 
% 1.13/1.35               (k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X18)))
% 1.13/1.35          | ((k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X16))
% 1.13/1.35              = (k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X18)))
% 1.13/1.35          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 1.13/1.35          | ~ (l1_pre_topc @ X17)
% 1.13/1.35          | ~ (v3_tdlat_3 @ X17)
% 1.13/1.35          | ~ (v2_pre_topc @ X17)
% 1.13/1.35          | (v2_struct_0 @ X17))),
% 1.13/1.35      inference('cnf', [status(esa)], [t55_tex_2])).
% 1.13/1.35  thf('41', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X2 @ 
% 1.13/1.35           (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)))
% 1.13/1.35          | (v2_struct_0 @ X1)
% 1.13/1.35          | ~ (v2_pre_topc @ X1)
% 1.13/1.35          | ~ (v3_tdlat_3 @ X1)
% 1.13/1.35          | ~ (l1_pre_topc @ X1)
% 1.13/1.35          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.13/1.35          | ((k2_pre_topc @ X1 @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ X1) @ 
% 1.13/1.35               (sk_C @ 
% 1.13/1.35                (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)) @ 
% 1.13/1.35                X2)))
% 1.13/1.35              = (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)))
% 1.13/1.35          | ~ (m1_subset_1 @ 
% 1.13/1.35               (sk_C @ 
% 1.13/1.35                (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)) @ 
% 1.13/1.35                X2) @ 
% 1.13/1.35               (u1_struct_0 @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['39', '40'])).
% 1.13/1.35  thf('42', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r1_xboole_0 @ X0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | ((k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.35               (sk_C @ 
% 1.13/1.35                (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35                X0)))
% 1.13/1.35              = (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | ~ (l1_pre_topc @ sk_A)
% 1.13/1.35          | ~ (v3_tdlat_3 @ sk_A)
% 1.13/1.35          | ~ (v2_pre_topc @ sk_A)
% 1.13/1.35          | (v2_struct_0 @ sk_A)
% 1.13/1.35          | (r1_xboole_0 @ X0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['38', '41'])).
% 1.13/1.35  thf('43', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('45', plain, ((v3_tdlat_3 @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('47', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35          | (r1_xboole_0 @ X0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | ((k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.35               (sk_C @ 
% 1.13/1.35                (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35                X0)))
% 1.13/1.35              = (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | (v2_struct_0 @ sk_A)
% 1.13/1.35          | (r1_xboole_0 @ X0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.13/1.35      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 1.13/1.35  thf('48', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((v2_struct_0 @ sk_A)
% 1.13/1.35          | ((k2_pre_topc @ sk_A @ 
% 1.13/1.35              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.35               (sk_C @ 
% 1.13/1.35                (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35                X0)))
% 1.13/1.35              = (k2_pre_topc @ sk_A @ 
% 1.13/1.35                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | (r1_xboole_0 @ X0 @ 
% 1.13/1.35             (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['47'])).
% 1.13/1.35  thf('49', plain,
% 1.13/1.35      ((((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 1.13/1.35          = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | (r1_xboole_0 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35        | (v2_struct_0 @ sk_A)
% 1.13/1.35        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | (r1_xboole_0 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35        | (v2_struct_0 @ sk_A))),
% 1.13/1.35      inference('sup+', [status(thm)], ['24', '48'])).
% 1.13/1.35  thf('50', plain,
% 1.13/1.35      (((v2_struct_0 @ sk_A)
% 1.13/1.35        | (r1_xboole_0 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 1.13/1.35            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.13/1.35      inference('simplify', [status(thm)], ['49'])).
% 1.13/1.35  thf('51', plain,
% 1.13/1.35      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.13/1.35         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('52', plain,
% 1.13/1.35      (((v2_struct_0 @ sk_A)
% 1.13/1.35        | (r1_xboole_0 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.35        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 1.13/1.35  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('54', plain,
% 1.13/1.35      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | (r1_xboole_0 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.13/1.35      inference('clc', [status(thm)], ['52', '53'])).
% 1.13/1.35  thf('55', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.13/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.13/1.35  thf('56', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.13/1.35  thf('57', plain,
% 1.13/1.35      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X2 @ X0)
% 1.13/1.35          | ~ (r2_hidden @ X2 @ X3)
% 1.13/1.35          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.13/1.35      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.13/1.35  thf('58', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X1 @ X0)
% 1.13/1.35          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.13/1.35          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.13/1.35      inference('sup-', [status(thm)], ['56', '57'])).
% 1.13/1.35  thf('59', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_xboole_0 @ X0 @ X1)
% 1.13/1.35          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.13/1.35          | (r1_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['55', '58'])).
% 1.13/1.35  thf('60', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('simplify', [status(thm)], ['59'])).
% 1.13/1.35  thf('61', plain,
% 1.13/1.35      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.13/1.35        | (r1_xboole_0 @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['54', '60'])).
% 1.13/1.35  thf('62', plain,
% 1.13/1.35      (~ (r1_xboole_0 @ 
% 1.13/1.35          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.13/1.35          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('63', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.13/1.35      inference('clc', [status(thm)], ['61', '62'])).
% 1.13/1.35  thf(fc2_struct_0, axiom,
% 1.13/1.35    (![A:$i]:
% 1.13/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.13/1.35       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.13/1.35  thf('64', plain,
% 1.13/1.35      (![X13 : $i]:
% 1.13/1.35         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 1.13/1.35          | ~ (l1_struct_0 @ X13)
% 1.13/1.35          | (v2_struct_0 @ X13))),
% 1.13/1.35      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.13/1.35  thf('65', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 1.13/1.35      inference('sup-', [status(thm)], ['63', '64'])).
% 1.13/1.35  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(dt_l1_pre_topc, axiom,
% 1.13/1.35    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.13/1.35  thf('67', plain,
% 1.13/1.35      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 1.13/1.35      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.13/1.35  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 1.13/1.35      inference('sup-', [status(thm)], ['66', '67'])).
% 1.13/1.35  thf('69', plain, ((v2_struct_0 @ sk_A)),
% 1.13/1.35      inference('demod', [status(thm)], ['65', '68'])).
% 1.13/1.35  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 1.13/1.35  
% 1.13/1.35  % SZS output end Refutation
% 1.13/1.35  
% 1.13/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
