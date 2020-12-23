%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Cts9PfPC7

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 311 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  985 (4063 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(t32_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v4_pre_topc @ ( k1_connsp_2 @ A @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v4_pre_topc @ ( k1_connsp_2 @ A @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_connsp_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d7_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k1_connsp_2 @ A @ B ) )
              <=> ? [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                    & ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ E @ D )
                        <=> ( ( r2_hidden @ B @ E )
                            & ( v4_pre_topc @ E @ A )
                            & ( v3_pre_topc @ E @ A ) ) ) )
                    & ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ D )
                      = C ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ B @ A )
    <=> ( ( v3_pre_topc @ E @ A )
        & ( v4_pre_topc @ E @ A )
        & ( r2_hidden @ B @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k1_connsp_2 @ A @ B ) )
              <=> ? [D: $i] :
                    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ D )
                      = C )
                    & ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ E @ D )
                        <=> ( zip_tseitin_0 @ E @ B @ A ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( X8
       != ( k1_connsp_2 @ X7 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X7 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ X7 @ X6 ) @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(t44_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) )
           => ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v4_pre_topc @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('18',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( X8
       != ( k1_connsp_2 @ X7 @ X6 ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X7 ) @ ( sk_D @ X8 @ X6 @ X7 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X7 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X7 ) @ ( sk_D @ ( k1_connsp_2 @ X7 @ X6 ) @ X6 @ X7 ) )
        = ( k1_connsp_2 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      = ( k1_connsp_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      = ( k1_connsp_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    = ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','30'])).

thf('32',plain,(
    ~ ( v4_pre_topc @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X1 ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('36',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    = ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ~ ( v4_pre_topc @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( X8
       != ( k1_connsp_2 @ X7 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ ( sk_D @ X8 @ X6 @ X7 ) )
      | ( zip_tseitin_0 @ X9 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X7 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( zip_tseitin_0 @ X9 @ X6 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( sk_D @ ( k1_connsp_2 @ X7 @ X6 ) @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X1 ) @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('54',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    = ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ~ ( v4_pre_topc @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    zip_tseitin_0 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v4_pre_topc @ X2 @ X3 )
      | ~ ( zip_tseitin_0 @ X2 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,(
    v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['33','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Cts9PfPC7
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 25 iterations in 0.013s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.20/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.48  thf(t32_connsp_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( v4_pre_topc @ ( k1_connsp_2 @ A @ B ) @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( v4_pre_topc @ ( k1_connsp_2 @ A @ B ) @ A ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t32_connsp_2])).
% 0.20/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k1_connsp_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (v2_pre_topc @ X11)
% 0.20/0.48          | (v2_struct_0 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.20/0.48          | (m1_subset_1 @ (k1_connsp_2 @ X11 @ X12) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.48  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(d7_connsp_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( C ) = ( k1_connsp_2 @ A @ B ) ) <=>
% 0.20/0.48                 ( ?[D:$i]:
% 0.20/0.48                   ( ( m1_subset_1 @
% 0.20/0.48                       D @ 
% 0.20/0.48                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) & 
% 0.20/0.48                     ( ![E:$i]:
% 0.20/0.48                       ( ( m1_subset_1 @
% 0.20/0.48                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.48                           ( ( r2_hidden @ B @ E ) & ( v4_pre_topc @ E @ A ) & 
% 0.20/0.48                             ( v3_pre_topc @ E @ A ) ) ) ) ) & 
% 0.20/0.48                     ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ D ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_2, axiom,
% 0.20/0.48    (![E:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_0 @ E @ B @ A ) <=>
% 0.20/0.48       ( ( v3_pre_topc @ E @ A ) & ( v4_pre_topc @ E @ A ) & 
% 0.20/0.48         ( r2_hidden @ B @ E ) ) ))).
% 0.20/0.48  thf(zf_stmt_3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( C ) = ( k1_connsp_2 @ A @ B ) ) <=>
% 0.20/0.48                 ( ?[D:$i]:
% 0.20/0.48                   ( ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ D ) = ( C ) ) & 
% 0.20/0.48                     ( ![E:$i]:
% 0.20/0.48                       ( ( m1_subset_1 @
% 0.20/0.48                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.48                           ( zip_tseitin_0 @ E @ B @ A ) ) ) ) & 
% 0.20/0.48                     ( m1_subset_1 @
% 0.20/0.48                       D @ 
% 0.20/0.48                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ((X8) != (k1_connsp_2 @ X7 @ X6))
% 0.20/0.48          | (m1_subset_1 @ (sk_D @ X8 @ X6 @ X7) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | (v2_struct_0 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ (k1_connsp_2 @ X7 @ X6) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | (m1_subset_1 @ (sk_D @ (k1_connsp_2 @ X7 @ X6) @ X6 @ X7) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.48  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.20/0.48  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf(t44_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @
% 0.20/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48           ( ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) =>
% 0.20/0.48             ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.48          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X1) @ X0) @ X1)
% 0.20/0.48          | ~ (v4_pre_topc @ (sk_C @ X0 @ X1) @ X1)
% 0.20/0.48          | ~ (l1_pre_topc @ X1)
% 0.20/0.48          | ~ (v2_pre_topc @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v4_pre_topc @ 
% 0.20/0.48             (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48        | (v4_pre_topc @ 
% 0.20/0.48           (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ((X8) != (k1_connsp_2 @ X7 @ X6))
% 0.20/0.48          | ((k6_setfam_1 @ (u1_struct_0 @ X7) @ (sk_D @ X8 @ X6 @ X7)) = (X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | (v2_struct_0 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ (k1_connsp_2 @ X7 @ X6) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ((k6_setfam_1 @ (u1_struct_0 @ X7) @ 
% 0.20/0.48              (sk_D @ (k1_connsp_2 @ X7 @ X6) @ X6 @ X7))
% 0.20/0.48              = (k1_connsp_2 @ X7 @ X6))
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | ((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48            = (k1_connsp_2 @ sk_A @ sk_B))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.48  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48          (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48          = (k1_connsp_2 @ sk_A @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.20/0.48  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48         (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48         = (k1_connsp_2 @ sk_A @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((~ (v4_pre_topc @ 
% 0.20/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48           sk_A)
% 0.20/0.48        | (v4_pre_topc @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19', '20', '30'])).
% 0.20/0.48  thf('32', plain, (~ (v4_pre_topc @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (~ (v4_pre_topc @ 
% 0.20/0.48          (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48          sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.48          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X1) @ X0) @ X1)
% 0.20/0.48          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X1)
% 0.20/0.48          | ~ (v2_pre_topc @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (r2_hidden @ 
% 0.20/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48           (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48        | (v4_pre_topc @ 
% 0.20/0.48           (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48         (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48         = (k1_connsp_2 @ sk_A @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (((r2_hidden @ 
% 0.20/0.48         (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48         (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48        | (v4_pre_topc @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.20/0.48  thf('41', plain, (~ (v4_pre_topc @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((r2_hidden @ 
% 0.20/0.48        (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48        (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ((X8) != (k1_connsp_2 @ X7 @ X6))
% 0.20/0.48          | ~ (r2_hidden @ X9 @ (sk_D @ X8 @ X6 @ X7))
% 0.20/0.48          | (zip_tseitin_0 @ X9 @ X6 @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | (v2_struct_0 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ (k1_connsp_2 @ X7 @ X6) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | (zip_tseitin_0 @ X9 @ X6 @ X7)
% 0.20/0.48          | ~ (r2_hidden @ X9 @ (sk_D @ (k1_connsp_2 @ X7 @ X6) @ X6 @ X7))
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ 
% 0.20/0.48               (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48          | (zip_tseitin_0 @ X0 @ sk_B @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '45'])).
% 0.20/0.48  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ 
% 0.20/0.48             (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48          | (zip_tseitin_0 @ X0 @ sk_B @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (m1_subset_1 @ 
% 0.20/0.48             (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (zip_tseitin_0 @ 
% 0.20/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48           sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '50'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.48          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X1) @ X0) @ X1)
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ X0 @ X1) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.48          | ~ (l1_pre_topc @ X1)
% 0.20/0.48          | ~ (v2_pre_topc @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ 
% 0.20/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v4_pre_topc @ 
% 0.20/0.48           (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48         (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.20/0.48         = (k1_connsp_2 @ sk_A @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (((m1_subset_1 @ 
% 0.20/0.48         (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v4_pre_topc @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.20/0.48  thf('59', plain, (~ (v4_pre_topc @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      ((m1_subset_1 @ 
% 0.20/0.48        (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (zip_tseitin_0 @ 
% 0.20/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48           sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['51', '60'])).
% 0.20/0.48  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      ((zip_tseitin_0 @ 
% 0.20/0.48        (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48        sk_B @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         ((v4_pre_topc @ X2 @ X3) | ~ (zip_tseitin_0 @ X2 @ X4 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      ((v4_pre_topc @ 
% 0.20/0.48        (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.48        sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.48  thf('66', plain, ($false), inference('demod', [status(thm)], ['33', '65'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
