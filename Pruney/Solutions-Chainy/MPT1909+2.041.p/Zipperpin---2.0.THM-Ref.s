%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gcOjSdWbpj

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 153 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  888 (4061 expanded)
%              Number of equality atoms :   26 ( 120 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v4_tex_2 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( v3_borsuk_1 @ X13 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X14 != X15 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X13 @ X14 )
        = ( k2_pre_topc @ X12 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v5_pre_topc @ X13 @ X12 @ X11 )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v5_pre_topc @ X13 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X13 @ X15 )
        = ( k2_pre_topc @ X12 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_borsuk_1 @ X13 @ X12 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( v4_tex_2 @ X11 @ X12 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24','25','26','27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('34',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('46',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gcOjSdWbpj
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:48:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 56 iterations in 0.034s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(t77_tex_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.49         ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.49             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.49                 ( m1_subset_1 @
% 0.20/0.49                   C @ 
% 0.20/0.49                   ( k1_zfmisc_1 @
% 0.20/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.49                 ( ![D:$i]:
% 0.20/0.49                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                     ( ![E:$i]:
% 0.20/0.49                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.49                           ( ( k8_relset_1 @
% 0.20/0.49                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.49                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.49                             ( k2_pre_topc @
% 0.20/0.49                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.49                ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.49                    ( v1_funct_2 @
% 0.20/0.49                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.49                    ( m1_subset_1 @
% 0.20/0.49                      C @ 
% 0.20/0.49                      ( k1_zfmisc_1 @
% 0.20/0.49                        ( k2_zfmisc_1 @
% 0.20/0.49                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.49                    ( ![D:$i]:
% 0.20/0.49                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                        ( ![E:$i]:
% 0.20/0.49                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                            ( ( ( D ) = ( E ) ) =>
% 0.20/0.49                              ( ( k8_relset_1 @
% 0.20/0.49                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.49                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.49                                ( k2_pre_topc @
% 0.20/0.49                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.20/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain, (((sk_D) = (sk_E))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X10 @ X9)
% 0.20/0.49          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(t2_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r2_hidden @ X3 @ X4)
% 0.20/0.49          | (v1_xboole_0 @ X4)
% 0.20/0.49          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(t63_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r2_hidden @ X3 @ X4)
% 0.20/0.49          | (v1_xboole_0 @ X4)
% 0.20/0.49          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t76_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.49         ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.49             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.49                 ( m1_subset_1 @
% 0.20/0.49                   C @ 
% 0.20/0.49                   ( k1_zfmisc_1 @
% 0.20/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.49                 ( ![D:$i]:
% 0.20/0.49                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.49                     ( ![E:$i]:
% 0.20/0.49                       ( ( m1_subset_1 @
% 0.20/0.49                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.49                           ( ( k8_relset_1 @
% 0.20/0.49                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.49                               D ) =
% 0.20/0.49                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X11)
% 0.20/0.49          | ~ (v4_tex_2 @ X11 @ X12)
% 0.20/0.49          | ~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.49          | ~ (v3_borsuk_1 @ X13 @ X12 @ X11)
% 0.20/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.49          | ((X14) != (X15))
% 0.20/0.49          | ((k8_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13 @ 
% 0.20/0.49              X14) = (k2_pre_topc @ X12 @ X15))
% 0.20/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))))
% 0.20/0.49          | ~ (v5_pre_topc @ X13 @ X12 @ X11)
% 0.20/0.49          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (l1_pre_topc @ X12)
% 0.20/0.49          | ~ (v3_tdlat_3 @ X12)
% 0.20/0.49          | ~ (v2_pre_topc @ X12)
% 0.20/0.49          | (v2_struct_0 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X12)
% 0.20/0.49          | ~ (v2_pre_topc @ X12)
% 0.20/0.49          | ~ (v3_tdlat_3 @ X12)
% 0.20/0.49          | ~ (l1_pre_topc @ X12)
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 0.20/0.49          | ~ (v5_pre_topc @ X13 @ X12 @ X11)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))))
% 0.20/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.49          | ((k8_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13 @ 
% 0.20/0.49              X15) = (k2_pre_topc @ X12 @ X15))
% 0.20/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.49          | ~ (v3_borsuk_1 @ X13 @ X12 @ X11)
% 0.20/0.49          | ~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.49          | ~ (v4_tex_2 @ X11 @ X12)
% 0.20/0.49          | (v2_struct_0 @ X11))),
% 0.20/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.20/0.49          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.49          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.49          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.49  thf('20', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.49          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['19', '20', '21', '22', '23', '24', '25', '26', '27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.49            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.49        | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.49            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '30'])).
% 0.20/0.49  thf('32', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X10 @ X9)
% 0.20/0.49          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.49         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.49         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain, (((sk_D) = (sk_E))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.49         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.49         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.49          (k1_tarski @ sk_D))
% 0.20/0.49          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.49          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.49            != (k2_pre_topc @ sk_A @ 
% 0.20/0.49                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.49          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.49  thf(fc2_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X8 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (l1_struct_0 @ X8)
% 0.20/0.49          | (v2_struct_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('46', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['44', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.49  thf('50', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.49  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X8 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (l1_struct_0 @ X8)
% 0.20/0.49          | (v2_struct_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('55', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_m1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('58', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.49  thf('61', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain, ((v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['55', '62'])).
% 0.20/0.49  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
