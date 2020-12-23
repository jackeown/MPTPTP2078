%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PuBxy8pYxR

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:28 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 210 expanded)
%              Number of leaves         :   34 (  74 expanded)
%              Depth                    :   22
%              Number of atoms          : 1195 (3990 expanded)
%              Number of equality atoms :   16 (  81 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ X22 @ ( k1_connsp_2 @ X23 @ X22 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_B_2 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
      | ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_tdlat_3 @ X24 )
      | ~ ( v4_pre_topc @ X25 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

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

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ X28 )
      | ( r1_xboole_0 @ X26 @ ( k2_pre_topc @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['24','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('63',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('66',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['60','70'])).

thf('72',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

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

thf('73',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r2_hidden @ X29 @ ( k2_pre_topc @ X30 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X31 ) ) )
      | ( ( k2_pre_topc @ X30 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) )
        = ( k2_pre_topc @ X30 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v3_tdlat_3 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    v1_xboole_0 @ ( k1_connsp_2 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['19','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['9','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PuBxy8pYxR
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.75  % Solved by: fo/fo7.sh
% 0.57/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.75  % done 440 iterations in 0.299s
% 0.57/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.75  % SZS output start Refutation
% 0.57/0.75  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.57/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.57/0.75  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.57/0.75  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.57/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.57/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.75  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.57/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.75  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.57/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.57/0.75  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.57/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.75  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.57/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.75  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.57/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.75  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.57/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.75  thf(t56_tex_2, conjecture,
% 0.57/0.75    (![A:$i]:
% 0.57/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.57/0.75         ( l1_pre_topc @ A ) ) =>
% 0.57/0.75       ( ![B:$i]:
% 0.57/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.75           ( ![C:$i]:
% 0.57/0.75             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.75               ( ( r1_xboole_0 @
% 0.57/0.75                   ( k2_pre_topc @
% 0.57/0.75                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.57/0.75                   ( k2_pre_topc @
% 0.57/0.75                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.57/0.75                 ( ( k2_pre_topc @
% 0.57/0.75                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.57/0.75                   ( k2_pre_topc @
% 0.57/0.75                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.57/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.75    (~( ![A:$i]:
% 0.57/0.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.57/0.75            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.75          ( ![B:$i]:
% 0.57/0.75            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.75              ( ![C:$i]:
% 0.57/0.75                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.75                  ( ( r1_xboole_0 @
% 0.57/0.75                      ( k2_pre_topc @
% 0.57/0.75                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.57/0.75                      ( k2_pre_topc @
% 0.57/0.75                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.57/0.75                    ( ( k2_pre_topc @
% 0.57/0.75                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.57/0.75                      ( k2_pre_topc @
% 0.57/0.75                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.57/0.75    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.57/0.75  thf('0', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(t30_connsp_2, axiom,
% 0.57/0.75    (![A:$i]:
% 0.57/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.75       ( ![B:$i]:
% 0.57/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.75           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.57/0.75  thf('1', plain,
% 0.57/0.75      (![X22 : $i, X23 : $i]:
% 0.57/0.75         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.57/0.75          | (r2_hidden @ X22 @ (k1_connsp_2 @ X23 @ X22))
% 0.57/0.75          | ~ (l1_pre_topc @ X23)
% 0.57/0.75          | ~ (v2_pre_topc @ X23)
% 0.57/0.75          | (v2_struct_0 @ X23))),
% 0.57/0.75      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.57/0.75  thf('2', plain,
% 0.57/0.75      (((v2_struct_0 @ sk_A)
% 0.57/0.75        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.75        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.75        | (r2_hidden @ sk_B_2 @ (k1_connsp_2 @ sk_A @ sk_B_2)))),
% 0.57/0.75      inference('sup-', [status(thm)], ['0', '1'])).
% 0.57/0.75  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('5', plain,
% 0.57/0.75      (((v2_struct_0 @ sk_A)
% 0.57/0.75        | (r2_hidden @ sk_B_2 @ (k1_connsp_2 @ sk_A @ sk_B_2)))),
% 0.57/0.75      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.57/0.75  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('7', plain, ((r2_hidden @ sk_B_2 @ (k1_connsp_2 @ sk_A @ sk_B_2))),
% 0.57/0.75      inference('clc', [status(thm)], ['5', '6'])).
% 0.57/0.75  thf(d1_xboole_0, axiom,
% 0.57/0.75    (![A:$i]:
% 0.57/0.75     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.57/0.75  thf('8', plain,
% 0.57/0.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.57/0.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.57/0.75  thf('9', plain, (~ (v1_xboole_0 @ (k1_connsp_2 @ sk_A @ sk_B_2))),
% 0.57/0.75      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.75  thf('10', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(dt_k1_connsp_2, axiom,
% 0.57/0.75    (![A:$i,B:$i]:
% 0.57/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.57/0.75         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.75       ( m1_subset_1 @
% 0.57/0.75         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.57/0.75  thf('11', plain,
% 0.57/0.75      (![X20 : $i, X21 : $i]:
% 0.57/0.75         (~ (l1_pre_topc @ X20)
% 0.57/0.75          | ~ (v2_pre_topc @ X20)
% 0.57/0.75          | (v2_struct_0 @ X20)
% 0.57/0.75          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.57/0.75          | (m1_subset_1 @ (k1_connsp_2 @ X20 @ X21) @ 
% 0.57/0.75             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.57/0.75      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.57/0.75  thf('12', plain,
% 0.57/0.75      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B_2) @ 
% 0.57/0.75         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.75        | (v2_struct_0 @ sk_A)
% 0.57/0.75        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.75        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.75      inference('sup-', [status(thm)], ['10', '11'])).
% 0.57/0.75  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('15', plain,
% 0.57/0.75      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B_2) @ 
% 0.57/0.75         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.75        | (v2_struct_0 @ sk_A))),
% 0.57/0.75      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.57/0.75  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('17', plain,
% 0.57/0.75      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B_2) @ 
% 0.57/0.75        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.75      inference('clc', [status(thm)], ['15', '16'])).
% 0.57/0.75  thf(cc1_subset_1, axiom,
% 0.57/0.75    (![A:$i]:
% 0.57/0.75     ( ( v1_xboole_0 @ A ) =>
% 0.57/0.75       ( ![B:$i]:
% 0.57/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.57/0.75  thf('18', plain,
% 0.57/0.75      (![X10 : $i, X11 : $i]:
% 0.57/0.75         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.57/0.75          | (v1_xboole_0 @ X10)
% 0.57/0.75          | ~ (v1_xboole_0 @ X11))),
% 0.57/0.75      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.57/0.75  thf('19', plain,
% 0.57/0.75      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.75        | (v1_xboole_0 @ (k1_connsp_2 @ sk_A @ sk_B_2)))),
% 0.57/0.75      inference('sup-', [status(thm)], ['17', '18'])).
% 0.57/0.75  thf('20', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(t2_subset, axiom,
% 0.57/0.75    (![A:$i,B:$i]:
% 0.57/0.75     ( ( m1_subset_1 @ A @ B ) =>
% 0.57/0.75       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.57/0.75  thf('21', plain,
% 0.59/0.75      (![X12 : $i, X13 : $i]:
% 0.59/0.75         ((r2_hidden @ X12 @ X13)
% 0.59/0.75          | (v1_xboole_0 @ X13)
% 0.59/0.75          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.59/0.75      inference('cnf', [status(esa)], [t2_subset])).
% 0.59/0.75  thf('22', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.75  thf(t63_subset_1, axiom,
% 0.59/0.75    (![A:$i,B:$i]:
% 0.59/0.75     ( ( r2_hidden @ A @ B ) =>
% 0.59/0.75       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.59/0.75  thf('23', plain,
% 0.59/0.75      (![X8 : $i, X9 : $i]:
% 0.59/0.75         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.59/0.75          | ~ (r2_hidden @ X8 @ X9))),
% 0.59/0.75      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.59/0.75  thf('24', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.59/0.75           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.75      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.75  thf(l27_zfmisc_1, axiom,
% 0.59/0.75    (![A:$i,B:$i]:
% 0.59/0.75     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.59/0.75  thf('25', plain,
% 0.59/0.75      (![X6 : $i, X7 : $i]:
% 0.59/0.75         ((r1_xboole_0 @ (k1_tarski @ X6) @ X7) | (r2_hidden @ X6 @ X7))),
% 0.59/0.75      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.59/0.75  thf(symmetry_r1_xboole_0, axiom,
% 0.59/0.75    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.59/0.75  thf('26', plain,
% 0.59/0.75      (![X3 : $i, X4 : $i]:
% 0.59/0.75         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.59/0.75      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.59/0.75  thf('27', plain,
% 0.59/0.75      (![X0 : $i, X1 : $i]:
% 0.59/0.75         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.75  thf('28', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('29', plain,
% 0.59/0.75      (![X12 : $i, X13 : $i]:
% 0.59/0.75         ((r2_hidden @ X12 @ X13)
% 0.59/0.75          | (v1_xboole_0 @ X13)
% 0.59/0.75          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.59/0.75      inference('cnf', [status(esa)], [t2_subset])).
% 0.59/0.75  thf('30', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.75  thf('31', plain,
% 0.59/0.75      (![X8 : $i, X9 : $i]:
% 0.59/0.75         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.59/0.75          | ~ (r2_hidden @ X8 @ X9))),
% 0.59/0.75      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.59/0.75  thf('32', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.59/0.75           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.75      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.75  thf(dt_k2_pre_topc, axiom,
% 0.59/0.75    (![A:$i,B:$i]:
% 0.59/0.75     ( ( ( l1_pre_topc @ A ) & 
% 0.59/0.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.75       ( m1_subset_1 @
% 0.59/0.75         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.75  thf('33', plain,
% 0.59/0.75      (![X14 : $i, X15 : $i]:
% 0.59/0.75         (~ (l1_pre_topc @ X14)
% 0.59/0.75          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.59/0.75          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 0.59/0.75             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.59/0.75      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.59/0.75  thf('34', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.75        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.75      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.75  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('36', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.75      inference('demod', [status(thm)], ['34', '35'])).
% 0.59/0.75  thf(t24_tdlat_3, axiom,
% 0.59/0.75    (![A:$i]:
% 0.59/0.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.75       ( ( v3_tdlat_3 @ A ) <=>
% 0.59/0.75         ( ![B:$i]:
% 0.59/0.75           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.75             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.59/0.75  thf('37', plain,
% 0.59/0.75      (![X24 : $i, X25 : $i]:
% 0.59/0.75         (~ (v3_tdlat_3 @ X24)
% 0.59/0.75          | ~ (v4_pre_topc @ X25 @ X24)
% 0.59/0.75          | (v3_pre_topc @ X25 @ X24)
% 0.59/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.59/0.75          | ~ (l1_pre_topc @ X24)
% 0.59/0.75          | ~ (v2_pre_topc @ X24))),
% 0.59/0.75      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.59/0.75  thf('38', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.75        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.75        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.59/0.75        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.59/0.75        | ~ (v3_tdlat_3 @ sk_A))),
% 0.59/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.75  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('41', plain, ((v3_tdlat_3 @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('42', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.59/0.75        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.59/0.75      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.59/0.75  thf('43', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.59/0.75           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.75      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.75  thf(fc1_tops_1, axiom,
% 0.59/0.75    (![A:$i,B:$i]:
% 0.59/0.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.59/0.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.75       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.59/0.75  thf('44', plain,
% 0.59/0.75      (![X18 : $i, X19 : $i]:
% 0.59/0.75         (~ (l1_pre_topc @ X18)
% 0.59/0.75          | ~ (v2_pre_topc @ X18)
% 0.59/0.75          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.75          | (v4_pre_topc @ (k2_pre_topc @ X18 @ X19) @ X18))),
% 0.59/0.75      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.59/0.75  thf('45', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.59/0.75        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.75        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.75      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.75  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('48', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.59/0.75      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.59/0.75  thf('49', plain,
% 0.59/0.75      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('clc', [status(thm)], ['42', '48'])).
% 0.59/0.75  thf('50', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.75      inference('demod', [status(thm)], ['34', '35'])).
% 0.59/0.75  thf(t40_tsep_1, axiom,
% 0.59/0.75    (![A:$i]:
% 0.59/0.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.75       ( ![B:$i]:
% 0.59/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.75           ( ![C:$i]:
% 0.59/0.75             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.75               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.59/0.75                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.59/0.75  thf('51', plain,
% 0.59/0.75      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.75         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.59/0.75          | ~ (v3_pre_topc @ X26 @ X27)
% 0.59/0.75          | ~ (r1_xboole_0 @ X26 @ X28)
% 0.59/0.75          | (r1_xboole_0 @ X26 @ (k2_pre_topc @ X27 @ X28))
% 0.59/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.59/0.75          | ~ (l1_pre_topc @ X27)
% 0.59/0.75          | ~ (v2_pre_topc @ X27))),
% 0.59/0.75      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.59/0.75  thf('52', plain,
% 0.59/0.75      (![X0 : $i]:
% 0.59/0.75         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.75          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.75          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75             (k2_pre_topc @ sk_A @ X0))
% 0.59/0.75          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.59/0.75          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.59/0.75      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.75  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('55', plain,
% 0.59/0.75      (![X0 : $i]:
% 0.59/0.75         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.75          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75             (k2_pre_topc @ sk_A @ X0))
% 0.59/0.75          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.59/0.75          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.59/0.75      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.59/0.75  thf('56', plain,
% 0.59/0.75      (![X0 : $i]:
% 0.59/0.75         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.59/0.75          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75             (k2_pre_topc @ sk_A @ X0))
% 0.59/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['49', '55'])).
% 0.59/0.75  thf('57', plain,
% 0.59/0.75      (![X0 : $i]:
% 0.59/0.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.75          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75             (k2_pre_topc @ sk_A @ X0))
% 0.59/0.75          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.59/0.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('simplify', [status(thm)], ['56'])).
% 0.59/0.75  thf('58', plain,
% 0.59/0.75      (![X0 : $i]:
% 0.59/0.75         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.59/0.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.59/0.75          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.59/0.75               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.75      inference('sup-', [status(thm)], ['27', '57'])).
% 0.59/0.75  thf('59', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.59/0.75      inference('sup-', [status(thm)], ['24', '58'])).
% 0.59/0.75  thf('60', plain,
% 0.59/0.75      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.59/0.75        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('simplify', [status(thm)], ['59'])).
% 0.59/0.75  thf('61', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf(redefinition_k6_domain_1, axiom,
% 0.59/0.75    (![A:$i,B:$i]:
% 0.59/0.75     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.59/0.75       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.59/0.75  thf('62', plain,
% 0.59/0.75      (![X16 : $i, X17 : $i]:
% 0.59/0.75         ((v1_xboole_0 @ X16)
% 0.59/0.75          | ~ (m1_subset_1 @ X17 @ X16)
% 0.59/0.75          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.59/0.75      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.59/0.75  thf('63', plain,
% 0.59/0.75      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['61', '62'])).
% 0.59/0.75  thf('64', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('65', plain,
% 0.59/0.75      (![X16 : $i, X17 : $i]:
% 0.59/0.75         ((v1_xboole_0 @ X16)
% 0.59/0.75          | ~ (m1_subset_1 @ X17 @ X16)
% 0.59/0.75          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.59/0.75      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.59/0.75  thf('66', plain,
% 0.59/0.75      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.75  thf('67', plain,
% 0.59/0.75      (~ (r1_xboole_0 @ 
% 0.59/0.75          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.59/0.75          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('68', plain,
% 0.59/0.75      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['66', '67'])).
% 0.59/0.75  thf('69', plain,
% 0.59/0.75      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['63', '68'])).
% 0.59/0.75  thf('70', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.59/0.75             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C))))),
% 0.59/0.75      inference('simplify', [status(thm)], ['69'])).
% 0.59/0.75  thf('71', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.59/0.75      inference('clc', [status(thm)], ['60', '70'])).
% 0.59/0.75  thf('72', plain,
% 0.59/0.75      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.75  thf(t55_tex_2, axiom,
% 0.59/0.75    (![A:$i]:
% 0.59/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.59/0.75         ( l1_pre_topc @ A ) ) =>
% 0.59/0.75       ( ![B:$i]:
% 0.59/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.75           ( ![C:$i]:
% 0.59/0.75             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.75               ( ( r2_hidden @
% 0.59/0.75                   B @ 
% 0.59/0.75                   ( k2_pre_topc @
% 0.59/0.75                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.59/0.75                 ( ( k2_pre_topc @
% 0.59/0.75                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.59/0.75                   ( k2_pre_topc @
% 0.59/0.75                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.59/0.75  thf('73', plain,
% 0.59/0.75      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.75         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.59/0.75          | ~ (r2_hidden @ X29 @ 
% 0.59/0.75               (k2_pre_topc @ X30 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X31)))
% 0.59/0.75          | ((k2_pre_topc @ X30 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29))
% 0.59/0.75              = (k2_pre_topc @ X30 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X31)))
% 0.59/0.75          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.59/0.75          | ~ (l1_pre_topc @ X30)
% 0.59/0.75          | ~ (v3_tdlat_3 @ X30)
% 0.59/0.75          | ~ (v2_pre_topc @ X30)
% 0.59/0.75          | (v2_struct_0 @ X30))),
% 0.59/0.75      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.59/0.75  thf('74', plain,
% 0.59/0.75      (![X0 : $i]:
% 0.59/0.75         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.59/0.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75          | (v2_struct_0 @ sk_A)
% 0.59/0.75          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.75          | ~ (v3_tdlat_3 @ sk_A)
% 0.59/0.75          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.75          | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.59/0.75          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.59/0.75              = (k2_pre_topc @ sk_A @ 
% 0.59/0.75                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.59/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['72', '73'])).
% 0.59/0.75  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('76', plain, ((v3_tdlat_3 @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('78', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('79', plain,
% 0.59/0.75      (![X0 : $i]:
% 0.59/0.75         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.59/0.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75          | (v2_struct_0 @ sk_A)
% 0.59/0.75          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.59/0.75              = (k2_pre_topc @ sk_A @ 
% 0.59/0.75                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.59/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 0.59/0.75  thf('80', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.59/0.75            = (k2_pre_topc @ sk_A @ 
% 0.59/0.75               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.59/0.75        | (v2_struct_0 @ sk_A)
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['71', '79'])).
% 0.59/0.75  thf('81', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('82', plain,
% 0.59/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.75        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.59/0.75            = (k2_pre_topc @ sk_A @ 
% 0.59/0.75               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.59/0.75        | (v2_struct_0 @ sk_A)
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('demod', [status(thm)], ['80', '81'])).
% 0.59/0.75  thf('83', plain,
% 0.59/0.75      (((v2_struct_0 @ sk_A)
% 0.59/0.75        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.59/0.75            = (k2_pre_topc @ sk_A @ 
% 0.59/0.75               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.59/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('simplify', [status(thm)], ['82'])).
% 0.59/0.75  thf('84', plain,
% 0.59/0.75      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.59/0.75         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('85', plain,
% 0.59/0.75      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.75      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 0.59/0.75  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('87', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.59/0.75      inference('clc', [status(thm)], ['85', '86'])).
% 0.59/0.75  thf('88', plain, ((v1_xboole_0 @ (k1_connsp_2 @ sk_A @ sk_B_2))),
% 0.59/0.75      inference('demod', [status(thm)], ['19', '87'])).
% 0.59/0.75  thf('89', plain, ($false), inference('demod', [status(thm)], ['9', '88'])).
% 0.59/0.75  
% 0.59/0.75  % SZS output end Refutation
% 0.59/0.75  
% 0.59/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
