%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2L8LKVnOc4

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:30 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 204 expanded)
%              Number of leaves         :   32 (  71 expanded)
%              Depth                    :   24
%              Number of atoms          : 1107 (3865 expanded)
%              Number of equality atoms :   23 (  94 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ ( k1_tarski @ X6 ) )
        = X5 )
      | ( r2_hidden @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k4_xboole_0 @ X0 @ X2 )
       != X0 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('15',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v4_pre_topc @ X18 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t40_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_xboole_0 @ B @ C )
                  & ( v3_pre_topc @ B @ A ) )
               => ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_xboole_0 @ X19 @ ( k2_pre_topc @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('50',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['48','54'])).

thf('56',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

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

thf('57',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_hidden @ X22 @ ( k2_pre_topc @ X23 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X24 ) ) )
      | ( ( k2_pre_topc @ X23 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) )
        = ( k2_pre_topc @ X23 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v3_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('72',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('75',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2L8LKVnOc4
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.72  % Solved by: fo/fo7.sh
% 0.54/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.72  % done 342 iterations in 0.265s
% 0.54/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.72  % SZS output start Refutation
% 0.54/0.72  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.54/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.54/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.54/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.54/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.72  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.54/0.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.54/0.72  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.54/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.54/0.72  thf(t56_tex_2, conjecture,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.54/0.72         ( l1_pre_topc @ A ) ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.72           ( ![C:$i]:
% 0.54/0.72             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.72               ( ( r1_xboole_0 @
% 0.54/0.72                   ( k2_pre_topc @
% 0.54/0.72                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.54/0.72                   ( k2_pre_topc @
% 0.54/0.72                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.54/0.72                 ( ( k2_pre_topc @
% 0.54/0.72                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.54/0.72                   ( k2_pre_topc @
% 0.54/0.72                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.54/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.72    (~( ![A:$i]:
% 0.54/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.54/0.72            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.72          ( ![B:$i]:
% 0.54/0.72            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.72              ( ![C:$i]:
% 0.54/0.72                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.72                  ( ( r1_xboole_0 @
% 0.54/0.72                      ( k2_pre_topc @
% 0.54/0.72                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.54/0.72                      ( k2_pre_topc @
% 0.54/0.72                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.54/0.72                    ( ( k2_pre_topc @
% 0.54/0.72                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.54/0.72                      ( k2_pre_topc @
% 0.54/0.72                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.54/0.72    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.54/0.72  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(redefinition_k6_domain_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.54/0.72       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.54/0.72  thf('2', plain,
% 0.54/0.72      (![X13 : $i, X14 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ X13)
% 0.54/0.72          | ~ (m1_subset_1 @ X14 @ X13)
% 0.54/0.72          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.54/0.72      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.54/0.72  thf('3', plain,
% 0.54/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.72  thf('4', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(dt_k6_domain_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.54/0.72       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.54/0.72  thf('5', plain,
% 0.54/0.72      (![X11 : $i, X12 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ X11)
% 0.54/0.72          | ~ (m1_subset_1 @ X12 @ X11)
% 0.54/0.72          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.54/0.72      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.54/0.72  thf('6', plain,
% 0.54/0.72      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.54/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.72  thf('7', plain,
% 0.54/0.72      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.54/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['3', '6'])).
% 0.54/0.72  thf('8', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.54/0.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.72      inference('simplify', [status(thm)], ['7'])).
% 0.54/0.72  thf(t65_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.54/0.72       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.54/0.72  thf('9', plain,
% 0.54/0.72      (![X5 : $i, X6 : $i]:
% 0.54/0.72         (((k4_xboole_0 @ X5 @ (k1_tarski @ X6)) = (X5))
% 0.54/0.72          | (r2_hidden @ X6 @ X5))),
% 0.54/0.72      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.54/0.72  thf(t83_xboole_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.72  thf('10', plain,
% 0.54/0.72      (![X0 : $i, X2 : $i]:
% 0.54/0.72         ((r1_xboole_0 @ X0 @ X2) | ((k4_xboole_0 @ X0 @ X2) != (X0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.54/0.72  thf('11', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((X0) != (X0))
% 0.54/0.72          | (r2_hidden @ X1 @ X0)
% 0.54/0.72          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.72  thf('12', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['11'])).
% 0.54/0.72  thf('13', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('14', plain,
% 0.54/0.72      (![X13 : $i, X14 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ X13)
% 0.54/0.72          | ~ (m1_subset_1 @ X14 @ X13)
% 0.54/0.72          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.54/0.72      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.54/0.72  thf('15', plain,
% 0.54/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.72  thf('16', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('17', plain,
% 0.54/0.72      (![X11 : $i, X12 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ X11)
% 0.54/0.72          | ~ (m1_subset_1 @ X12 @ X11)
% 0.54/0.72          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.54/0.72      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.54/0.72  thf('18', plain,
% 0.54/0.72      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.54/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.54/0.72  thf('19', plain,
% 0.54/0.72      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.54/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['15', '18'])).
% 0.54/0.72  thf('20', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.54/0.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.72      inference('simplify', [status(thm)], ['19'])).
% 0.54/0.72  thf(dt_k2_pre_topc, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( l1_pre_topc @ A ) & 
% 0.54/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.72       ( m1_subset_1 @
% 0.54/0.72         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.54/0.72  thf('21', plain,
% 0.54/0.72      (![X7 : $i, X8 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X7)
% 0.54/0.72          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.54/0.72          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.54/0.72             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.54/0.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.54/0.72  thf('22', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.72  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('24', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.72  thf(t24_tdlat_3, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.72       ( ( v3_tdlat_3 @ A ) <=>
% 0.54/0.72         ( ![B:$i]:
% 0.54/0.72           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.72             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.54/0.72  thf('25', plain,
% 0.54/0.72      (![X17 : $i, X18 : $i]:
% 0.54/0.72         (~ (v3_tdlat_3 @ X17)
% 0.54/0.72          | ~ (v4_pre_topc @ X18 @ X17)
% 0.54/0.72          | (v3_pre_topc @ X18 @ X17)
% 0.54/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.54/0.72          | ~ (l1_pre_topc @ X17)
% 0.54/0.72          | ~ (v2_pre_topc @ X17))),
% 0.54/0.72      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.54/0.72  thf('26', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.54/0.72        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.54/0.72        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.54/0.72        | ~ (v3_tdlat_3 @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.72  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('29', plain, ((v3_tdlat_3 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('30', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.54/0.72        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.54/0.72      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.54/0.72  thf('31', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.54/0.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.72      inference('simplify', [status(thm)], ['19'])).
% 0.54/0.72  thf(fc1_tops_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.54/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.72       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.54/0.72  thf('32', plain,
% 0.54/0.72      (![X15 : $i, X16 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X15)
% 0.54/0.72          | ~ (v2_pre_topc @ X15)
% 0.54/0.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.54/0.72          | (v4_pre_topc @ (k2_pre_topc @ X15 @ X16) @ X15))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.54/0.72  thf('33', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.54/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.72  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('36', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.54/0.72      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.54/0.72  thf('37', plain,
% 0.54/0.72      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('clc', [status(thm)], ['30', '36'])).
% 0.54/0.72  thf('38', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.72  thf(t40_tsep_1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.72           ( ![C:$i]:
% 0.54/0.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.72               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.54/0.72                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.54/0.72  thf('39', plain,
% 0.54/0.72      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.54/0.72          | ~ (v3_pre_topc @ X19 @ X20)
% 0.54/0.72          | ~ (r1_xboole_0 @ X19 @ X21)
% 0.54/0.72          | (r1_xboole_0 @ X19 @ (k2_pre_topc @ X20 @ X21))
% 0.54/0.72          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.54/0.72          | ~ (l1_pre_topc @ X20)
% 0.54/0.72          | ~ (v2_pre_topc @ X20))),
% 0.54/0.72      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.54/0.72  thf('40', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.54/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.54/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72             (k2_pre_topc @ sk_A @ X0))
% 0.54/0.72          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.54/0.72          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.72  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('43', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72             (k2_pre_topc @ sk_A @ X0))
% 0.54/0.72          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.54/0.72          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.54/0.72      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.54/0.72  thf('44', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.54/0.72          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72             (k2_pre_topc @ sk_A @ X0))
% 0.54/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['37', '43'])).
% 0.54/0.72  thf('45', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.72          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72             (k2_pre_topc @ sk_A @ X0))
% 0.54/0.72          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.54/0.72          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['44'])).
% 0.54/0.72  thf('46', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.54/0.72          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.54/0.72          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.54/0.72               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['12', '45'])).
% 0.54/0.72  thf('47', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['8', '46'])).
% 0.54/0.72  thf('48', plain,
% 0.54/0.72      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.54/0.72        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.72  thf('49', plain,
% 0.54/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.72  thf('50', plain,
% 0.54/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.72  thf('51', plain,
% 0.54/0.72      (~ (r1_xboole_0 @ 
% 0.54/0.72          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.54/0.72          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('52', plain,
% 0.54/0.72      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.54/0.72  thf('53', plain,
% 0.54/0.72      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['49', '52'])).
% 0.54/0.72  thf('54', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.54/0.72             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C))))),
% 0.54/0.72      inference('simplify', [status(thm)], ['53'])).
% 0.54/0.72  thf('55', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.54/0.72      inference('clc', [status(thm)], ['48', '54'])).
% 0.54/0.72  thf('56', plain,
% 0.54/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.72  thf(t55_tex_2, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.54/0.72         ( l1_pre_topc @ A ) ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.72           ( ![C:$i]:
% 0.54/0.72             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.72               ( ( r2_hidden @
% 0.54/0.72                   B @ 
% 0.54/0.72                   ( k2_pre_topc @
% 0.54/0.72                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.54/0.72                 ( ( k2_pre_topc @
% 0.54/0.72                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.54/0.72                   ( k2_pre_topc @
% 0.54/0.72                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.54/0.72  thf('57', plain,
% 0.54/0.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.54/0.72          | ~ (r2_hidden @ X22 @ 
% 0.54/0.72               (k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X24)))
% 0.54/0.72          | ((k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22))
% 0.54/0.72              = (k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X24)))
% 0.54/0.72          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.54/0.72          | ~ (l1_pre_topc @ X23)
% 0.54/0.72          | ~ (v3_tdlat_3 @ X23)
% 0.54/0.72          | ~ (v2_pre_topc @ X23)
% 0.54/0.72          | (v2_struct_0 @ X23))),
% 0.54/0.72      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.54/0.72  thf('58', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.54/0.72          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72          | (v2_struct_0 @ sk_A)
% 0.54/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.54/0.72          | ~ (v3_tdlat_3 @ sk_A)
% 0.54/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.54/0.72          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.54/0.72          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.54/0.72              = (k2_pre_topc @ sk_A @ 
% 0.54/0.72                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.54/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.72  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('60', plain, ((v3_tdlat_3 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('62', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('63', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.54/0.72          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72          | (v2_struct_0 @ sk_A)
% 0.54/0.72          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.54/0.72              = (k2_pre_topc @ sk_A @ 
% 0.54/0.72                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.54/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.54/0.72  thf('64', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.54/0.72            = (k2_pre_topc @ sk_A @ 
% 0.54/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.54/0.72        | (v2_struct_0 @ sk_A)
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['55', '63'])).
% 0.54/0.72  thf('65', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('66', plain,
% 0.54/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.72        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.54/0.72            = (k2_pre_topc @ sk_A @ 
% 0.54/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.54/0.72        | (v2_struct_0 @ sk_A)
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['64', '65'])).
% 0.54/0.72  thf('67', plain,
% 0.54/0.72      (((v2_struct_0 @ sk_A)
% 0.54/0.72        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.54/0.72            = (k2_pre_topc @ sk_A @ 
% 0.54/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.54/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['66'])).
% 0.54/0.72  thf('68', plain,
% 0.54/0.72      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.72         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('69', plain,
% 0.54/0.72      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.54/0.72  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('71', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.54/0.72      inference('clc', [status(thm)], ['69', '70'])).
% 0.54/0.72  thf(fc2_struct_0, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.54/0.72       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.54/0.72  thf('72', plain,
% 0.54/0.72      (![X10 : $i]:
% 0.54/0.72         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.54/0.72          | ~ (l1_struct_0 @ X10)
% 0.54/0.72          | (v2_struct_0 @ X10))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.54/0.72  thf('73', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['71', '72'])).
% 0.54/0.72  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(dt_l1_pre_topc, axiom,
% 0.54/0.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.54/0.72  thf('75', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.54/0.72      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.54/0.72  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.72      inference('sup-', [status(thm)], ['74', '75'])).
% 0.54/0.72  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 0.54/0.72      inference('demod', [status(thm)], ['73', '76'])).
% 0.54/0.72  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
