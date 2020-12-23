%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b6IDqGaE0w

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:28 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 182 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   23
%              Number of atoms          : 1052 (3343 expanded)
%              Number of equality atoms :   16 (  69 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
      | ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v4_pre_topc @ X21 @ X20 )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_xboole_0 @ X22 @ ( k2_pre_topc @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('44',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('47',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['41','51'])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

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

thf('54',plain,(
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

thf('55',plain,(
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('69',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('72',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b6IDqGaE0w
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:38:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 196 iterations in 0.119s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.37/0.56  thf(t56_tex_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.37/0.56         ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56               ( ( r1_xboole_0 @
% 0.37/0.56                   ( k2_pre_topc @
% 0.37/0.56                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.37/0.56                   ( k2_pre_topc @
% 0.37/0.56                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.37/0.56                 ( ( k2_pre_topc @
% 0.37/0.56                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.37/0.56                   ( k2_pre_topc @
% 0.37/0.56                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56                  ( ( r1_xboole_0 @
% 0.37/0.56                      ( k2_pre_topc @
% 0.37/0.56                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.37/0.56                      ( k2_pre_topc @
% 0.37/0.56                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.37/0.56                    ( ( k2_pre_topc @
% 0.37/0.56                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.37/0.56                      ( k2_pre_topc @
% 0.37/0.56                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.37/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t2_subset, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((r2_hidden @ X10 @ X11)
% 0.37/0.56          | (v1_xboole_0 @ X11)
% 0.37/0.56          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf(t63_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.56       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.37/0.56          | ~ (r2_hidden @ X8 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf(l27_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ (k1_tarski @ X6) @ X7) | (r2_hidden @ X6 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.37/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('9', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((r2_hidden @ X10 @ X11)
% 0.37/0.56          | (v1_xboole_0 @ X11)
% 0.37/0.56          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.37/0.56          | ~ (r2_hidden @ X8 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf(dt_k2_pre_topc, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56       ( m1_subset_1 @
% 0.37/0.56         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X12)
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf(t24_tdlat_3, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ( v3_tdlat_3 @ A ) <=>
% 0.37/0.56         ( ![B:$i]:
% 0.37/0.56           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         (~ (v3_tdlat_3 @ X20)
% 0.37/0.56          | ~ (v4_pre_topc @ X21 @ X20)
% 0.37/0.56          | (v3_pre_topc @ X21 @ X20)
% 0.37/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.56          | ~ (l1_pre_topc @ X20)
% 0.37/0.56          | ~ (v2_pre_topc @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.37/0.56        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.37/0.56        | ~ (v3_tdlat_3 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('22', plain, ((v3_tdlat_3 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.37/0.56        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf(fc1_tops_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.37/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X18)
% 0.37/0.56          | ~ (v2_pre_topc @ X18)
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | (v4_pre_topc @ (k2_pre_topc @ X18 @ X19) @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['23', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf(t40_tsep_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.37/0.56                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.56          | ~ (v3_pre_topc @ X22 @ X23)
% 0.37/0.56          | ~ (r1_xboole_0 @ X22 @ X24)
% 0.37/0.56          | (r1_xboole_0 @ X22 @ (k2_pre_topc @ X23 @ X24))
% 0.37/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.56          | ~ (l1_pre_topc @ X23)
% 0.37/0.56          | ~ (v2_pre_topc @ X23))),
% 0.37/0.56      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56             (k2_pre_topc @ sk_A @ X0))
% 0.37/0.56          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.37/0.56          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.56  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56             (k2_pre_topc @ sk_A @ X0))
% 0.37/0.56          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.37/0.56          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.37/0.56          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56             (k2_pre_topc @ sk_A @ X0))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['30', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56             (k2_pre_topc @ sk_A @ X0))
% 0.37/0.56          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.37/0.56          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '39'])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.37/0.56        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['40'])).
% 0.37/0.56  thf('42', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X16 : $i, X17 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X16)
% 0.37/0.56          | ~ (m1_subset_1 @ X17 @ X16)
% 0.37/0.56          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('45', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X16 : $i, X17 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X16)
% 0.37/0.56          | ~ (m1_subset_1 @ X17 @ X16)
% 0.37/0.56          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (~ (r1_xboole_0 @ 
% 0.37/0.56          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.37/0.56          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['44', '49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.37/0.56             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.37/0.56      inference('clc', [status(thm)], ['41', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf(t55_tex_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.37/0.56         ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56               ( ( r2_hidden @
% 0.37/0.56                   B @ 
% 0.37/0.56                   ( k2_pre_topc @
% 0.37/0.56                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.37/0.56                 ( ( k2_pre_topc @
% 0.37/0.56                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.37/0.56                   ( k2_pre_topc @
% 0.37/0.56                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.37/0.56          | ~ (r2_hidden @ X25 @ 
% 0.37/0.56               (k2_pre_topc @ X26 @ (k6_domain_1 @ (u1_struct_0 @ X26) @ X27)))
% 0.37/0.56          | ((k2_pre_topc @ X26 @ (k6_domain_1 @ (u1_struct_0 @ X26) @ X25))
% 0.37/0.56              = (k2_pre_topc @ X26 @ (k6_domain_1 @ (u1_struct_0 @ X26) @ X27)))
% 0.37/0.56          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.37/0.56          | ~ (l1_pre_topc @ X26)
% 0.37/0.56          | ~ (v3_tdlat_3 @ X26)
% 0.37/0.56          | ~ (v2_pre_topc @ X26)
% 0.37/0.56          | (v2_struct_0 @ X26))),
% 0.37/0.56      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (v3_tdlat_3 @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.37/0.56              = (k2_pre_topc @ sk_A @ 
% 0.37/0.56                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.56  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('57', plain, ((v3_tdlat_3 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('59', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.37/0.56              = (k2_pre_topc @ sk_A @ 
% 0.37/0.56                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.56            = (k2_pre_topc @ sk_A @ 
% 0.37/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '60'])).
% 0.37/0.56  thf('62', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.56            = (k2_pre_topc @ sk_A @ 
% 0.37/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.56            = (k2_pre_topc @ sk_A @ 
% 0.37/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['63'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.37/0.56         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.37/0.56  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('68', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['66', '67'])).
% 0.37/0.56  thf(fc2_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (![X15 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.37/0.56          | ~ (l1_struct_0 @ X15)
% 0.37/0.56          | (v2_struct_0 @ X15))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.56  thf('70', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.56  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_l1_pre_topc, axiom,
% 0.37/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.56  thf('74', plain, ((v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['70', '73'])).
% 0.37/0.56  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
