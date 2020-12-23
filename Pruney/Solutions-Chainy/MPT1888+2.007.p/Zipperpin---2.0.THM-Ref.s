%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iq4mCdoIKw

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:28 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 208 expanded)
%              Number of leaves         :   32 (  72 expanded)
%              Depth                    :   24
%              Number of atoms          : 1145 (3921 expanded)
%              Number of equality atoms :   24 (  95 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('18',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v4_pre_topc @ X21 @ X20 )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_xboole_0 @ X22 @ ( k2_pre_topc @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_C_2 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('54',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['51','57'])).

thf('59',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

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

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r2_hidden @ X25 @ ( k2_pre_topc @ X26 @ ( k6_domain_1 @ ( u1_struct_0 @ X26 ) @ X27 ) ) )
      | ( ( k2_pre_topc @ X26 @ ( k6_domain_1 @ ( u1_struct_0 @ X26 ) @ X25 ) )
        = ( k2_pre_topc @ X26 @ ( k6_domain_1 @ ( u1_struct_0 @ X26 ) @ X27 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v3_tdlat_3 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('61',plain,(
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
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('78',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iq4mCdoIKw
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:07:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.60/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.77  % Solved by: fo/fo7.sh
% 0.60/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.77  % done 499 iterations in 0.318s
% 0.60/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.77  % SZS output start Refutation
% 0.60/0.77  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.60/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.77  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.60/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.77  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.60/0.77  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.60/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.77  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.60/0.77  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.60/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.60/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.77  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.60/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.77  thf(t56_tex_2, conjecture,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.60/0.77         ( l1_pre_topc @ A ) ) =>
% 0.60/0.77       ( ![B:$i]:
% 0.60/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.77           ( ![C:$i]:
% 0.60/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.77               ( ( r1_xboole_0 @
% 0.60/0.77                   ( k2_pre_topc @
% 0.60/0.77                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.60/0.77                   ( k2_pre_topc @
% 0.60/0.77                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.60/0.77                 ( ( k2_pre_topc @
% 0.60/0.77                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.60/0.77                   ( k2_pre_topc @
% 0.60/0.77                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.60/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.77    (~( ![A:$i]:
% 0.60/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.77            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.77          ( ![B:$i]:
% 0.60/0.77            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.77              ( ![C:$i]:
% 0.60/0.77                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.77                  ( ( r1_xboole_0 @
% 0.60/0.77                      ( k2_pre_topc @
% 0.60/0.77                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.60/0.77                      ( k2_pre_topc @
% 0.60/0.77                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.60/0.77                    ( ( k2_pre_topc @
% 0.60/0.77                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.60/0.77                      ( k2_pre_topc @
% 0.60/0.77                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.60/0.77    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.60/0.77  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(redefinition_k6_domain_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.60/0.77       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.60/0.77  thf('2', plain,
% 0.60/0.77      (![X16 : $i, X17 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ X16)
% 0.60/0.77          | ~ (m1_subset_1 @ X17 @ X16)
% 0.60/0.77          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.60/0.77      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.60/0.77  thf('3', plain,
% 0.60/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.77  thf('4', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(dt_k6_domain_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.60/0.77       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.60/0.77  thf('5', plain,
% 0.60/0.77      (![X14 : $i, X15 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ X14)
% 0.60/0.77          | ~ (m1_subset_1 @ X15 @ X14)
% 0.60/0.77          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 0.60/0.77      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.60/0.77  thf('6', plain,
% 0.60/0.77      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ 
% 0.60/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.77  thf('7', plain,
% 0.60/0.77      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.60/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['3', '6'])).
% 0.60/0.77  thf('8', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.60/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.77      inference('simplify', [status(thm)], ['7'])).
% 0.60/0.77  thf(t3_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.60/0.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.77            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.60/0.77  thf('9', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.60/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.77  thf(d1_tarski, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.60/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.60/0.77  thf('10', plain,
% 0.60/0.77      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.60/0.77      inference('cnf', [status(esa)], [d1_tarski])).
% 0.60/0.77  thf('11', plain,
% 0.60/0.77      (![X4 : $i, X7 : $i]:
% 0.60/0.77         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['10'])).
% 0.60/0.77  thf('12', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.60/0.77          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['9', '11'])).
% 0.60/0.77  thf('13', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.77  thf('14', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ X0 @ X1)
% 0.60/0.77          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.60/0.77          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['12', '13'])).
% 0.60/0.77  thf('15', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.60/0.77      inference('simplify', [status(thm)], ['14'])).
% 0.60/0.77  thf('16', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('17', plain,
% 0.60/0.77      (![X16 : $i, X17 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ X16)
% 0.60/0.77          | ~ (m1_subset_1 @ X17 @ X16)
% 0.60/0.77          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.60/0.77      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.60/0.77  thf('18', plain,
% 0.60/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.77  thf('19', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('20', plain,
% 0.60/0.77      (![X14 : $i, X15 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ X14)
% 0.60/0.77          | ~ (m1_subset_1 @ X15 @ X14)
% 0.60/0.77          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 0.60/0.77      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.60/0.77  thf('21', plain,
% 0.60/0.77      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.60/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.60/0.77  thf('22', plain,
% 0.60/0.77      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.60/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['18', '21'])).
% 0.60/0.77  thf('23', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.60/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.77      inference('simplify', [status(thm)], ['22'])).
% 0.60/0.77  thf(dt_k2_pre_topc, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ( l1_pre_topc @ A ) & 
% 0.60/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.77       ( m1_subset_1 @
% 0.60/0.77         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.77  thf('24', plain,
% 0.60/0.77      (![X10 : $i, X11 : $i]:
% 0.60/0.77         (~ (l1_pre_topc @ X10)
% 0.60/0.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.60/0.77          | (m1_subset_1 @ (k2_pre_topc @ X10 @ X11) @ 
% 0.60/0.77             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.60/0.77      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.60/0.77  thf('25', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.77  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('27', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.77  thf(t24_tdlat_3, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.77       ( ( v3_tdlat_3 @ A ) <=>
% 0.60/0.77         ( ![B:$i]:
% 0.60/0.77           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.77             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.60/0.77  thf('28', plain,
% 0.60/0.77      (![X20 : $i, X21 : $i]:
% 0.60/0.77         (~ (v3_tdlat_3 @ X20)
% 0.60/0.77          | ~ (v4_pre_topc @ X21 @ X20)
% 0.60/0.77          | (v3_pre_topc @ X21 @ X20)
% 0.60/0.77          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.60/0.77          | ~ (l1_pre_topc @ X20)
% 0.60/0.77          | ~ (v2_pre_topc @ X20))),
% 0.60/0.77      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.60/0.77  thf('29', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.77        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.60/0.77        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.60/0.77        | ~ (v3_tdlat_3 @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['27', '28'])).
% 0.60/0.77  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('33', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.60/0.77        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.60/0.77  thf('34', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.60/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.77      inference('simplify', [status(thm)], ['22'])).
% 0.60/0.77  thf(fc1_tops_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.60/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.77       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.60/0.77  thf('35', plain,
% 0.60/0.77      (![X18 : $i, X19 : $i]:
% 0.60/0.77         (~ (l1_pre_topc @ X18)
% 0.60/0.77          | ~ (v2_pre_topc @ X18)
% 0.60/0.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.60/0.77          | (v4_pre_topc @ (k2_pre_topc @ X18 @ X19) @ X18))),
% 0.60/0.77      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.60/0.77  thf('36', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.60/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.77        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.60/0.77  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('39', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.60/0.77  thf('40', plain,
% 0.60/0.77      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('clc', [status(thm)], ['33', '39'])).
% 0.60/0.77  thf('41', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.77  thf(t40_tsep_1, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.77       ( ![B:$i]:
% 0.60/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.77           ( ![C:$i]:
% 0.60/0.77             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.77               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.60/0.77                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.60/0.77  thf('42', plain,
% 0.60/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.77         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.60/0.77          | ~ (v3_pre_topc @ X22 @ X23)
% 0.60/0.77          | ~ (r1_xboole_0 @ X22 @ X24)
% 0.60/0.77          | (r1_xboole_0 @ X22 @ (k2_pre_topc @ X23 @ X24))
% 0.60/0.77          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.60/0.77          | ~ (l1_pre_topc @ X23)
% 0.60/0.77          | ~ (v2_pre_topc @ X23))),
% 0.60/0.77      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.60/0.77  thf('43', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77             (k2_pre_topc @ sk_A @ X0))
% 0.60/0.77          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.60/0.77          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['41', '42'])).
% 0.60/0.77  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('46', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77             (k2_pre_topc @ sk_A @ X0))
% 0.60/0.77          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.60/0.77          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.60/0.77  thf('47', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.60/0.77          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77             (k2_pre_topc @ sk_A @ X0))
% 0.60/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['40', '46'])).
% 0.60/0.77  thf('48', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.77          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77             (k2_pre_topc @ sk_A @ X0))
% 0.60/0.77          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.60/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['47'])).
% 0.60/0.77  thf('49', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.60/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.60/0.77          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.60/0.77               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.77      inference('sup-', [status(thm)], ['15', '48'])).
% 0.60/0.77  thf('50', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (r2_hidden @ sk_C_2 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.60/0.77      inference('sup-', [status(thm)], ['8', '49'])).
% 0.60/0.77  thf('51', plain,
% 0.60/0.77      (((r2_hidden @ sk_C_2 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.60/0.77        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['50'])).
% 0.60/0.77  thf('52', plain,
% 0.60/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.77  thf('53', plain,
% 0.60/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.77  thf('54', plain,
% 0.60/0.77      (~ (r1_xboole_0 @ 
% 0.60/0.77          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.60/0.77          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('55', plain,
% 0.60/0.77      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.77  thf('56', plain,
% 0.60/0.77      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['52', '55'])).
% 0.60/0.77  thf('57', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.60/0.77             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))))),
% 0.60/0.77      inference('simplify', [status(thm)], ['56'])).
% 0.60/0.77  thf('58', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | (r2_hidden @ sk_C_2 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.60/0.77      inference('clc', [status(thm)], ['51', '57'])).
% 0.60/0.77  thf('59', plain,
% 0.60/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.77  thf(t55_tex_2, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.60/0.77         ( l1_pre_topc @ A ) ) =>
% 0.60/0.77       ( ![B:$i]:
% 0.60/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.77           ( ![C:$i]:
% 0.60/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.77               ( ( r2_hidden @
% 0.60/0.77                   B @ 
% 0.60/0.77                   ( k2_pre_topc @
% 0.60/0.77                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.60/0.77                 ( ( k2_pre_topc @
% 0.60/0.77                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.60/0.77                   ( k2_pre_topc @
% 0.60/0.77                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.60/0.77  thf('60', plain,
% 0.60/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.77         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.60/0.77          | ~ (r2_hidden @ X25 @ 
% 0.60/0.77               (k2_pre_topc @ X26 @ (k6_domain_1 @ (u1_struct_0 @ X26) @ X27)))
% 0.60/0.77          | ((k2_pre_topc @ X26 @ (k6_domain_1 @ (u1_struct_0 @ X26) @ X25))
% 0.60/0.77              = (k2_pre_topc @ X26 @ (k6_domain_1 @ (u1_struct_0 @ X26) @ X27)))
% 0.60/0.77          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.60/0.77          | ~ (l1_pre_topc @ X26)
% 0.60/0.77          | ~ (v3_tdlat_3 @ X26)
% 0.60/0.77          | ~ (v2_pre_topc @ X26)
% 0.60/0.77          | (v2_struct_0 @ X26))),
% 0.60/0.77      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.60/0.77  thf('61', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.60/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77          | (v2_struct_0 @ sk_A)
% 0.60/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.77          | ~ (v3_tdlat_3 @ sk_A)
% 0.60/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.77          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.60/0.77          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.60/0.77              = (k2_pre_topc @ sk_A @ 
% 0.60/0.77                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.60/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['59', '60'])).
% 0.60/0.77  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('63', plain, ((v3_tdlat_3 @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('65', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('66', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.60/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77          | (v2_struct_0 @ sk_A)
% 0.60/0.77          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.60/0.77              = (k2_pre_topc @ sk_A @ 
% 0.60/0.77                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.60/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 0.60/0.77  thf('67', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | ~ (m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 0.60/0.77            = (k2_pre_topc @ sk_A @ 
% 0.60/0.77               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.60/0.77        | (v2_struct_0 @ sk_A)
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['58', '66'])).
% 0.60/0.77  thf('68', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('69', plain,
% 0.60/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.77        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 0.60/0.77            = (k2_pre_topc @ sk_A @ 
% 0.60/0.77               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.60/0.77        | (v2_struct_0 @ sk_A)
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('demod', [status(thm)], ['67', '68'])).
% 0.60/0.77  thf('70', plain,
% 0.60/0.77      (((v2_struct_0 @ sk_A)
% 0.60/0.77        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 0.60/0.77            = (k2_pre_topc @ sk_A @ 
% 0.60/0.77               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.60/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['69'])).
% 0.60/0.77  thf('71', plain,
% 0.60/0.77      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.60/0.77         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('72', plain,
% 0.60/0.77      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.77      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.60/0.77  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('74', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.60/0.77      inference('clc', [status(thm)], ['72', '73'])).
% 0.60/0.77  thf(fc2_struct_0, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.60/0.77       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.77  thf('75', plain,
% 0.60/0.77      (![X13 : $i]:
% 0.60/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.60/0.77          | ~ (l1_struct_0 @ X13)
% 0.60/0.77          | (v2_struct_0 @ X13))),
% 0.60/0.77      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.60/0.77  thf('76', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['74', '75'])).
% 0.60/0.77  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(dt_l1_pre_topc, axiom,
% 0.60/0.77    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.60/0.77  thf('78', plain,
% 0.60/0.77      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.60/0.77      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.60/0.77  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.77      inference('sup-', [status(thm)], ['77', '78'])).
% 0.60/0.77  thf('80', plain, ((v2_struct_0 @ sk_A)),
% 0.60/0.77      inference('demod', [status(thm)], ['76', '79'])).
% 0.60/0.77  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.60/0.77  
% 0.60/0.77  % SZS output end Refutation
% 0.60/0.77  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
