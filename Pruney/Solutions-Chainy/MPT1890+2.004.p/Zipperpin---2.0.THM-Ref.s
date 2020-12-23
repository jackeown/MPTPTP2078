%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7m4MU8x0Bx

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:31 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 259 expanded)
%              Number of leaves         :   24 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  845 (5469 expanded)
%              Number of equality atoms :   14 ( 130 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t58_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
             => ( v2_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_tex_2 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X15 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_tex_2 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X12 @ X13 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_tex_2 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ X14 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X13 ) @ ( sk_C @ X12 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('25',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','42'])).

thf('44',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_tdlat_3 @ X10 )
      | ~ ( v4_pre_topc @ X11 @ X10 )
      | ( v3_pre_topc @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X8 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','55','56'])).

thf('58',plain,(
    v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference('sup+',[status(thm)],['44','57'])).

thf('59',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','43','58'])).

thf('60',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7m4MU8x0Bx
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 345 iterations in 0.352s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.58/0.80  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.58/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.80  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.58/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.58/0.80  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.58/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.80  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.58/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(t58_tex_2, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.58/0.80         ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80           ( ( ![C:$i]:
% 0.58/0.80               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                 ( ( r2_hidden @ C @ B ) =>
% 0.58/0.80                   ( ( k9_subset_1 @
% 0.58/0.80                       ( u1_struct_0 @ A ) @ B @ 
% 0.58/0.80                       ( k2_pre_topc @
% 0.58/0.80                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.58/0.80                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.58/0.80             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.80            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80          ( ![B:$i]:
% 0.58/0.80            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80              ( ( ![C:$i]:
% 0.58/0.80                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                    ( ( r2_hidden @ C @ B ) =>
% 0.58/0.80                      ( ( k9_subset_1 @
% 0.58/0.80                          ( u1_struct_0 @ A ) @ B @ 
% 0.58/0.80                          ( k2_pre_topc @
% 0.58/0.80                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.58/0.80                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.58/0.80                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.58/0.80  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t37_tex_2, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80           ( ( ![C:$i]:
% 0.58/0.80               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.58/0.80                      ( ![D:$i]:
% 0.58/0.80                        ( ( m1_subset_1 @
% 0.58/0.80                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.58/0.80                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.58/0.80                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.58/0.80             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.80          | (v2_tex_2 @ X12 @ X13)
% 0.58/0.80          | (m1_subset_1 @ (sk_C @ X12 @ X13) @ (u1_struct_0 @ X13))
% 0.58/0.80          | ~ (l1_pre_topc @ X13)
% 0.58/0.80          | ~ (v2_pre_topc @ X13)
% 0.58/0.80          | (v2_struct_0 @ X13))),
% 0.58/0.80      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.80  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.58/0.80  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.80        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['6', '7'])).
% 0.58/0.80  thf('9', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['8', '9'])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (![X15 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X15 @ sk_B_1)
% 0.58/0.80          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X15)))
% 0.58/0.80              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X15))
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ 
% 0.58/0.80           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.58/0.80          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.58/0.80        | ~ (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.80          | (v2_tex_2 @ X12 @ X13)
% 0.58/0.80          | (r2_hidden @ (sk_C @ X12 @ X13) @ X12)
% 0.58/0.80          | ~ (l1_pre_topc @ X13)
% 0.58/0.80          | ~ (v2_pre_topc @ X13)
% 0.58/0.80          | (v2_struct_0 @ X13))),
% 0.58/0.80      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.58/0.80        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.80  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('18', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.58/0.80        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.58/0.80  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.80        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['18', '19'])).
% 0.58/0.80  thf('21', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('22', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.58/0.80      inference('clc', [status(thm)], ['20', '21'])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.58/0.80         (k2_pre_topc @ sk_A @ 
% 0.58/0.80          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['12', '22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.80          | (v2_tex_2 @ X12 @ X13)
% 0.58/0.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.80          | ~ (v3_pre_topc @ X14 @ X13)
% 0.58/0.80          | ((k9_subset_1 @ (u1_struct_0 @ X13) @ X12 @ X14)
% 0.58/0.80              != (k6_domain_1 @ (u1_struct_0 @ X13) @ (sk_C @ X12 @ X13)))
% 0.58/0.80          | ~ (l1_pre_topc @ X13)
% 0.58/0.80          | ~ (v2_pre_topc @ X13)
% 0.58/0.80          | (v2_struct_0 @ X13))),
% 0.58/0.80      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.80          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | ~ (v3_pre_topc @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.58/0.80             sk_A)
% 0.58/0.80        | ~ (m1_subset_1 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.58/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.80        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.80        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.80          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (v3_pre_topc @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.58/0.80             sk_A)
% 0.58/0.80        | ~ (m1_subset_1 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.58/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.80        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.80        | ~ (m1_subset_1 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.58/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.80        | ~ (v3_pre_topc @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.58/0.80             sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('simplify', [status(thm)], ['29'])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.58/0.80         (k2_pre_topc @ sk_A @ 
% 0.58/0.80          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['12', '22'])).
% 0.58/0.80  thf('32', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(commutativity_k9_subset_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.80       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.58/0.80  thf('33', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 0.58/0.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B_1)
% 0.58/0.80           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.80  thf('35', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(dt_k9_subset_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.80       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.80         ((m1_subset_1 @ (k9_subset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X3))
% 0.58/0.80          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.58/0.80  thf('37', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B_1) @ 
% 0.58/0.80          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.80  thf('38', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.58/0.80          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['34', '37'])).
% 0.58/0.80  thf(dt_k2_pre_topc, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( l1_pre_topc @ A ) & 
% 0.58/0.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.80       ( m1_subset_1 @
% 0.58/0.80         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.80  thf('39', plain,
% 0.58/0.80      (![X6 : $i, X7 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X6)
% 0.58/0.80          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.58/0.80          | (m1_subset_1 @ (k2_pre_topc @ X6 @ X7) @ 
% 0.58/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.58/0.80  thf('40', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((m1_subset_1 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ 
% 0.58/0.80            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)) @ 
% 0.58/0.80           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.80  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('42', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (m1_subset_1 @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ 
% 0.58/0.80           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)) @ 
% 0.58/0.80          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.58/0.80  thf('43', plain,
% 0.58/0.80      ((m1_subset_1 @ 
% 0.58/0.80        (k2_pre_topc @ sk_A @ 
% 0.58/0.80         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.58/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['31', '42'])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.58/0.80         (k2_pre_topc @ sk_A @ 
% 0.58/0.80          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['12', '22'])).
% 0.58/0.80  thf('45', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (m1_subset_1 @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ 
% 0.58/0.80           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)) @ 
% 0.58/0.80          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.58/0.80  thf(t24_tdlat_3, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ( v3_tdlat_3 @ A ) <=>
% 0.58/0.80         ( ![B:$i]:
% 0.58/0.80           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.58/0.80  thf('46', plain,
% 0.58/0.80      (![X10 : $i, X11 : $i]:
% 0.58/0.80         (~ (v3_tdlat_3 @ X10)
% 0.58/0.80          | ~ (v4_pre_topc @ X11 @ X10)
% 0.58/0.80          | (v3_pre_topc @ X11 @ X10)
% 0.58/0.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.58/0.80          | ~ (l1_pre_topc @ X10)
% 0.58/0.80          | ~ (v2_pre_topc @ X10))),
% 0.58/0.80      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.58/0.80  thf('47', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v2_pre_topc @ sk_A)
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80          | (v3_pre_topc @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)) @ 
% 0.58/0.80             sk_A)
% 0.58/0.80          | ~ (v4_pre_topc @ 
% 0.58/0.80               (k2_pre_topc @ sk_A @ 
% 0.58/0.80                (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)) @ 
% 0.58/0.80               sk_A)
% 0.58/0.80          | ~ (v3_tdlat_3 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.80  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.58/0.80          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['34', '37'])).
% 0.58/0.80  thf(fc1_tops_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.58/0.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.80       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X8)
% 0.58/0.80          | ~ (v2_pre_topc @ X8)
% 0.58/0.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.58/0.80          | (v4_pre_topc @ (k2_pre_topc @ X8 @ X9) @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v4_pre_topc @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ 
% 0.58/0.80            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)) @ 
% 0.58/0.80           sk_A)
% 0.58/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.80  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (v4_pre_topc @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ 
% 0.58/0.80           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)) @ 
% 0.58/0.80          sk_A)),
% 0.58/0.80      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.58/0.80  thf('56', plain, ((v3_tdlat_3 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('57', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (v3_pre_topc @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ 
% 0.58/0.80           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)) @ 
% 0.58/0.80          sk_A)),
% 0.58/0.80      inference('demod', [status(thm)], ['47', '48', '49', '55', '56'])).
% 0.58/0.80  thf('58', plain,
% 0.58/0.80      ((v3_pre_topc @ 
% 0.58/0.80        (k2_pre_topc @ sk_A @ 
% 0.58/0.80         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.58/0.80        sk_A)),
% 0.58/0.80      inference('sup+', [status(thm)], ['44', '57'])).
% 0.58/0.80  thf('59', plain, (((v2_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['30', '43', '58'])).
% 0.58/0.80  thf('60', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('61', plain, ((v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['59', '60'])).
% 0.58/0.80  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
