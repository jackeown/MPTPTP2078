%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fY2fzdl8yy

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:37 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 311 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  985 (4063 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( X6
       != ( k1_connsp_2 @ X5 @ X4 ) )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X5 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ X5 @ X4 ) @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ~ ( v4_pre_topc @ ( sk_C @ X11 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( X6
       != ( k1_connsp_2 @ X5 @ X4 ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X5 ) @ ( sk_D @ X6 @ X4 @ X5 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X5 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X5 ) @ ( sk_D @ ( k1_connsp_2 @ X5 @ X4 ) @ X4 @ X5 ) )
        = ( k1_connsp_2 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( X6
       != ( k1_connsp_2 @ X5 @ X4 ) )
      | ~ ( r2_hidden @ X7 @ ( sk_D @ X6 @ X4 @ X5 ) )
      | ( zip_tseitin_0 @ X7 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X5 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( zip_tseitin_0 @ X7 @ X4 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( sk_D @ ( k1_connsp_2 @ X5 @ X4 ) @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v4_pre_topc @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,(
    v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['33','65'])).


%------------------------------------------------------------------------------
