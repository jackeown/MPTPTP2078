%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hc3gN7IxDj

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:50 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 318 expanded)
%              Number of leaves         :   37 ( 108 expanded)
%              Depth                    :   22
%              Number of atoms          : 1166 (9571 expanded)
%              Number of equality atoms :   30 ( 267 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(t77_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                            = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_borsuk_1 @ C @ A @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( D = E )
                           => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                              = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t76_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                            = ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_tex_2 @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v3_borsuk_1 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( X24 != X25 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ X23 @ X24 )
        = ( k2_pre_topc @ X22 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v5_pre_topc @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v3_tdlat_3 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( v3_tdlat_3 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v5_pre_topc @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ X23 @ X25 )
        = ( k2_pre_topc @ X22 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_borsuk_1 @ X23 @ X22 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v4_tex_2 @ X21 @ X22 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23','24','25','26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( v4_tex_2 @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ( v3_tex_2 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v4_tex_2 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['30','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('64',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','64'])).

thf('66',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('67',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('76',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('84',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['0','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hc3gN7IxDj
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 116 iterations in 0.090s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.36/0.55  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.36/0.55  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(t77_tex_2, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.36/0.55         ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.36/0.55             ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.55                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.36/0.55                 ( m1_subset_1 @
% 0.36/0.55                   C @ 
% 0.36/0.55                   ( k1_zfmisc_1 @
% 0.36/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.55               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.36/0.55                 ( ![D:$i]:
% 0.36/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.55                     ( ![E:$i]:
% 0.36/0.55                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                         ( ( ( D ) = ( E ) ) =>
% 0.36/0.55                           ( ( k8_relset_1 @
% 0.36/0.55                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.55                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.36/0.55                             ( k2_pre_topc @
% 0.36/0.55                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.36/0.55                ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55                    ( v1_funct_2 @
% 0.36/0.55                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.55                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.36/0.55                    ( m1_subset_1 @
% 0.36/0.55                      C @ 
% 0.36/0.55                      ( k1_zfmisc_1 @
% 0.36/0.55                        ( k2_zfmisc_1 @
% 0.36/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.55                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.36/0.55                    ( ![D:$i]:
% 0.36/0.55                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.55                        ( ![E:$i]:
% 0.36/0.55                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                            ( ( ( D ) = ( E ) ) =>
% 0.36/0.55                              ( ( k8_relset_1 @
% 0.36/0.55                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.55                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.36/0.55                                ( k2_pre_topc @
% 0.36/0.55                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.36/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d1_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf('2', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('3', plain, (((sk_D) = (sk_E))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('4', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X12)
% 0.36/0.55          | ~ (m1_subset_1 @ X13 @ X12)
% 0.36/0.55          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf('7', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X12)
% 0.36/0.55          | ~ (m1_subset_1 @ X13 @ X12)
% 0.36/0.55          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k6_domain_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X10)
% 0.36/0.55          | ~ (m1_subset_1 @ X11 @ X10)
% 0.36/0.55          | (m1_subset_1 @ (k6_domain_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['9', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t76_tex_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.36/0.55         ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.36/0.55             ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.55                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.36/0.55                 ( m1_subset_1 @
% 0.36/0.55                   C @ 
% 0.36/0.55                   ( k1_zfmisc_1 @
% 0.36/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.55               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.36/0.55                 ( ![D:$i]:
% 0.36/0.55                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.55                     ( ![E:$i]:
% 0.36/0.55                       ( ( m1_subset_1 @
% 0.36/0.55                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55                         ( ( ( D ) = ( E ) ) =>
% 0.36/0.55                           ( ( k8_relset_1 @
% 0.36/0.55                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.55                               D ) =
% 0.36/0.55                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X21)
% 0.36/0.55          | ~ (v4_tex_2 @ X21 @ X22)
% 0.36/0.55          | ~ (m1_pre_topc @ X21 @ X22)
% 0.36/0.55          | ~ (v3_borsuk_1 @ X23 @ X22 @ X21)
% 0.36/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.36/0.55          | ((X24) != (X25))
% 0.36/0.55          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ X23 @ 
% 0.36/0.55              X24) = (k2_pre_topc @ X22 @ X25))
% 0.36/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.55          | ~ (m1_subset_1 @ X23 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.36/0.55          | ~ (v5_pre_topc @ X23 @ X22 @ X21)
% 0.36/0.55          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.36/0.55          | ~ (v1_funct_1 @ X23)
% 0.36/0.55          | ~ (l1_pre_topc @ X22)
% 0.36/0.55          | ~ (v3_tdlat_3 @ X22)
% 0.36/0.55          | ~ (v2_pre_topc @ X22)
% 0.36/0.55          | (v2_struct_0 @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X22)
% 0.36/0.55          | ~ (v2_pre_topc @ X22)
% 0.36/0.55          | ~ (v3_tdlat_3 @ X22)
% 0.36/0.55          | ~ (l1_pre_topc @ X22)
% 0.36/0.55          | ~ (v1_funct_1 @ X23)
% 0.36/0.55          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.36/0.55          | ~ (v5_pre_topc @ X23 @ X22 @ X21)
% 0.36/0.55          | ~ (m1_subset_1 @ X23 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.36/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.55          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ X23 @ 
% 0.36/0.55              X25) = (k2_pre_topc @ X22 @ X25))
% 0.36/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.36/0.55          | ~ (v3_borsuk_1 @ X23 @ X22 @ X21)
% 0.36/0.55          | ~ (m1_pre_topc @ X21 @ X22)
% 0.36/0.55          | ~ (v4_tex_2 @ X21 @ X22)
% 0.36/0.55          | (v2_struct_0 @ X21))),
% 0.36/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B_1)
% 0.36/0.55          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.55          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.55          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.55          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               (u1_struct_0 @ sk_B_1))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (v3_tdlat_3 @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['15', '17'])).
% 0.36/0.55  thf('19', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('20', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('21', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('22', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('24', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('26', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B_1)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.55          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)],
% 0.36/0.55                ['18', '19', '20', '21', '22', '23', '24', '25', '26', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55            sk_C_1 @ (k1_tarski @ sk_D))
% 0.36/0.55            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['14', '28'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('31', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf(t39_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.55               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X7 @ X8)
% 0.36/0.55          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.36/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.36/0.55          | ~ (l1_pre_topc @ X8))),
% 0.36/0.55      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.36/0.55          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '34'])).
% 0.36/0.55  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t1_tsep_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.55           ( m1_subset_1 @
% 0.36/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X14 : $i, X15 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X14 @ X15)
% 0.36/0.55          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.36/0.55          | ~ (l1_pre_topc @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.55  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf(t46_tex_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( v1_xboole_0 @ B ) & 
% 0.36/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (![X19 : $i, X20 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ X19)
% 0.36/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.55          | ~ (v3_tex_2 @ X19 @ X20)
% 0.36/0.55          | ~ (l1_pre_topc @ X20)
% 0.36/0.55          | ~ (v2_pre_topc @ X20)
% 0.36/0.55          | (v2_struct_0 @ X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.36/0.55        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.55  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.36/0.55        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.55  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['47', '48'])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf(d8_tex_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.55           ( ( v4_tex_2 @ B @ A ) <=>
% 0.36/0.55             ( ![C:$i]:
% 0.36/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X16 @ X17)
% 0.36/0.55          | ~ (v4_tex_2 @ X16 @ X17)
% 0.36/0.55          | ((X18) != (u1_struct_0 @ X16))
% 0.36/0.55          | (v3_tex_2 @ X18 @ X17)
% 0.36/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.55          | ~ (l1_pre_topc @ X17)
% 0.36/0.55          | (v2_struct_0 @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X17)
% 0.36/0.55          | ~ (l1_pre_topc @ X17)
% 0.36/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.36/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.55          | (v3_tex_2 @ (u1_struct_0 @ X16) @ X17)
% 0.36/0.55          | ~ (v4_tex_2 @ X16 @ X17)
% 0.36/0.55          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.36/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.55        | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.55        | (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['50', '52'])).
% 0.36/0.55  thf('54', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('55', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      (((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.36/0.55  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('59', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 0.36/0.55      inference('clc', [status(thm)], ['57', '58'])).
% 0.36/0.55  thf('60', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['49', '59'])).
% 0.36/0.55  thf('61', plain,
% 0.36/0.55      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('clc', [status(thm)], ['37', '60'])).
% 0.36/0.55  thf('62', plain,
% 0.36/0.55      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['30', '61'])).
% 0.36/0.55  thf('63', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['49', '59'])).
% 0.36/0.55  thf('64', plain,
% 0.36/0.55      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('clc', [status(thm)], ['62', '63'])).
% 0.36/0.55  thf('65', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55            sk_C_1 @ (k1_tarski @ sk_D))
% 0.36/0.55            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['29', '64'])).
% 0.36/0.55  thf('66', plain,
% 0.36/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('67', plain,
% 0.36/0.55      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55         sk_C_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.36/0.55         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('68', plain, (((sk_D) = (sk_E))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55         sk_C_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.36/0.55         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.36/0.55  thf('70', plain,
% 0.36/0.55      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55          sk_C_1 @ (k1_tarski @ sk_D))
% 0.36/0.55          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['66', '69'])).
% 0.36/0.55  thf('71', plain,
% 0.36/0.55      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.36/0.55          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['65', '70'])).
% 0.36/0.55  thf('72', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.36/0.55            != (k2_pre_topc @ sk_A @ 
% 0.36/0.55                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.36/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.36/0.55  thf('73', plain,
% 0.36/0.55      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.36/0.55          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['6', '72'])).
% 0.36/0.55  thf('74', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.36/0.55  thf('75', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf(t5_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.55  thf('76', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ X5)
% 0.36/0.55          | ~ (v1_xboole_0 @ X6)
% 0.36/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.55  thf('77', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.55  thf('78', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B_1)
% 0.36/0.55          | (v2_struct_0 @ sk_A)
% 0.36/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['74', '77'])).
% 0.36/0.55  thf('79', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '78'])).
% 0.36/0.55  thf('80', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['79'])).
% 0.36/0.55  thf('81', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('82', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['80', '81'])).
% 0.36/0.55  thf('83', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['49', '59'])).
% 0.36/0.55  thf('84', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('clc', [status(thm)], ['82', '83'])).
% 0.36/0.55  thf('85', plain, ($false), inference('demod', [status(thm)], ['0', '84'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
