%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V2xvDTpb8P

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:31 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 246 expanded)
%              Number of leaves         :   22 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  803 (5389 expanded)
%              Number of equality atoms :   15 ( 129 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_tex_2 @ X10 @ X11 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ X13 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X13 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_tex_2 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X10 @ X11 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_tex_2 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X12 @ X11 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 @ X12 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X11 ) @ ( sk_C @ X10 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','45'])).

thf('47',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

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
      ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ sk_A )
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
      ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A ),
    inference('sup+',[status(thm)],['47','55'])).

thf('57',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','46','56'])).

thf('58',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V2xvDTpb8P
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 128 iterations in 0.073s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.35/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(t58_tex_2, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.35/0.54         ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( ![C:$i]:
% 0.35/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.54                 ( ( r2_hidden @ C @ B ) =>
% 0.35/0.54                   ( ( k9_subset_1 @
% 0.35/0.54                       ( u1_struct_0 @ A ) @ B @ 
% 0.35/0.54                       ( k2_pre_topc @
% 0.35/0.54                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.35/0.54                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.35/0.54             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.54            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54              ( ( ![C:$i]:
% 0.35/0.54                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.54                    ( ( r2_hidden @ C @ B ) =>
% 0.35/0.54                      ( ( k9_subset_1 @
% 0.35/0.54                          ( u1_struct_0 @ A ) @ B @ 
% 0.35/0.54                          ( k2_pre_topc @
% 0.35/0.54                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.35/0.54                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.35/0.54                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.35/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t57_tex_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.35/0.54         ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( ![C:$i]:
% 0.35/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.54                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.35/0.54                      ( ![D:$i]:
% 0.35/0.54                        ( ( m1_subset_1 @
% 0.35/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.35/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.35/0.54                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.35/0.54             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.54          | (v2_tex_2 @ X10 @ X11)
% 0.35/0.54          | (m1_subset_1 @ (sk_C @ X10 @ X11) @ (u1_struct_0 @ X11))
% 0.35/0.54          | ~ (l1_pre_topc @ X11)
% 0.35/0.54          | ~ (v3_tdlat_3 @ X11)
% 0.35/0.54          | ~ (v2_pre_topc @ X11)
% 0.35/0.54          | (v2_struct_0 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54        | ~ (v3_tdlat_3 @ sk_A)
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.54  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('5', plain, ((v3_tdlat_3 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.35/0.54  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (((v2_tex_2 @ sk_B @ sk_A)
% 0.35/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.35/0.54  thf('10', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('clc', [status(thm)], ['9', '10'])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X13 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X13 @ sk_B)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X13)))
% 0.35/0.54              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X13))
% 0.35/0.54          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54          (k2_pre_topc @ sk_A @ 
% 0.35/0.54           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.35/0.54          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.35/0.54        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.54          | (v2_tex_2 @ X10 @ X11)
% 0.35/0.54          | (r2_hidden @ (sk_C @ X10 @ X11) @ X10)
% 0.35/0.54          | ~ (l1_pre_topc @ X11)
% 0.35/0.54          | ~ (v3_tdlat_3 @ X11)
% 0.35/0.54          | ~ (v2_pre_topc @ X11)
% 0.35/0.54          | (v2_struct_0 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54        | ~ (v3_tdlat_3 @ sk_A)
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.35/0.54        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.54  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('18', plain, ((v3_tdlat_3 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.35/0.54        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.35/0.54  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (((v2_tex_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.35/0.54      inference('clc', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('24', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.35/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54         (k2_pre_topc @ sk_A @ 
% 0.35/0.54          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.35/0.54         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.54          | (v2_tex_2 @ X10 @ X11)
% 0.35/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.54          | ~ (v4_pre_topc @ X12 @ X11)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X11) @ X10 @ X12)
% 0.35/0.54              != (k6_domain_1 @ (u1_struct_0 @ X11) @ (sk_C @ X10 @ X11)))
% 0.35/0.54          | ~ (l1_pre_topc @ X11)
% 0.35/0.54          | ~ (v3_tdlat_3 @ X11)
% 0.35/0.54          | ~ (v2_pre_topc @ X11)
% 0.35/0.54          | (v2_struct_0 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.35/0.54          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54        | ~ (v3_tdlat_3 @ sk_A)
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | ~ (v4_pre_topc @ 
% 0.35/0.54             (k2_pre_topc @ sk_A @ 
% 0.35/0.54              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.35/0.54             sk_A)
% 0.35/0.54        | ~ (m1_subset_1 @ 
% 0.35/0.54             (k2_pre_topc @ sk_A @ 
% 0.35/0.54              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54        | (v2_tex_2 @ sk_B @ sk_A)
% 0.35/0.54        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.54  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('29', plain, ((v3_tdlat_3 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.35/0.54          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | ~ (v4_pre_topc @ 
% 0.35/0.54             (k2_pre_topc @ sk_A @ 
% 0.35/0.54              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.35/0.54             sk_A)
% 0.35/0.54        | ~ (m1_subset_1 @ 
% 0.35/0.54             (k2_pre_topc @ sk_A @ 
% 0.35/0.54              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (((v2_tex_2 @ sk_B @ sk_A)
% 0.35/0.54        | ~ (m1_subset_1 @ 
% 0.35/0.54             (k2_pre_topc @ sk_A @ 
% 0.35/0.54              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54        | ~ (v4_pre_topc @ 
% 0.35/0.54             (k2_pre_topc @ sk_A @ 
% 0.35/0.54              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.35/0.54             sk_A)
% 0.35/0.54        | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54         (k2_pre_topc @ sk_A @ 
% 0.35/0.54          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.35/0.54         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '24'])).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(commutativity_k9_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.35/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(dt_k9_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (k9_subset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X3))
% 0.35/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.35/0.54  thf(dt_k2_pre_topc, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54       ( m1_subset_1 @
% 0.35/0.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X6)
% 0.35/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.35/0.54          | (m1_subset_1 @ (k2_pre_topc @ X6 @ X7) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_subset_1 @ 
% 0.35/0.54           (k2_pre_topc @ sk_A @ 
% 0.35/0.54            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.54  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (m1_subset_1 @ 
% 0.35/0.54          (k2_pre_topc @ sk_A @ 
% 0.35/0.54           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (m1_subset_1 @ 
% 0.35/0.54          (k2_pre_topc @ sk_A @ 
% 0.35/0.54           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['37', '44'])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      ((m1_subset_1 @ 
% 0.35/0.54        (k2_pre_topc @ sk_A @ 
% 0.35/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['34', '45'])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54         (k2_pre_topc @ sk_A @ 
% 0.35/0.54          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.35/0.54         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '24'])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.35/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['48', '49'])).
% 0.35/0.54  thf(fc1_tops_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X8)
% 0.35/0.54          | ~ (v2_pre_topc @ X8)
% 0.35/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.35/0.54          | (v4_pre_topc @ (k2_pre_topc @ X8 @ X9) @ X8))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v4_pre_topc @ 
% 0.35/0.54           (k2_pre_topc @ sk_A @ 
% 0.35/0.54            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.35/0.54           sk_A)
% 0.35/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54          | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.54  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('55', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (v4_pre_topc @ 
% 0.35/0.54          (k2_pre_topc @ sk_A @ 
% 0.35/0.54           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.35/0.54          sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.35/0.54  thf('56', plain,
% 0.35/0.54      ((v4_pre_topc @ 
% 0.35/0.54        (k2_pre_topc @ sk_A @ 
% 0.35/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.35/0.54        sk_A)),
% 0.35/0.54      inference('sup+', [status(thm)], ['47', '55'])).
% 0.35/0.54  thf('57', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['33', '46', '56'])).
% 0.35/0.54  thf('58', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('59', plain, ((v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('clc', [status(thm)], ['57', '58'])).
% 0.35/0.54  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
