%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KXqMWd3l24

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 441 expanded)
%              Number of leaves         :   25 ( 138 expanded)
%              Depth                    :   17
%              Number of atoms          : 1030 (5776 expanded)
%              Number of equality atoms :   12 (  47 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( X11
       != ( k1_connsp_2 @ X10 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X10 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ X10 @ X9 ) @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
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

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( v2_tops_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(t29_tops_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
           => ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X4 ) @ X3 ) @ X4 )
      | ~ ( v2_tops_2 @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_2])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( X11
       != ( k1_connsp_2 @ X10 @ X9 ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X10 ) @ ( sk_D @ X11 @ X9 @ X10 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X10 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X10 ) @ ( sk_D @ ( k1_connsp_2 @ X10 @ X9 ) @ X9 @ X10 ) )
        = ( k1_connsp_2 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      = ( k1_connsp_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      = ( k1_connsp_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    = ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','35'])).

thf('37',plain,(
    ~ ( v4_pre_topc @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['20','38'])).

thf('40',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( v2_tops_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('46',plain,(
    r2_hidden @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( X11
       != ( k1_connsp_2 @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( zip_tseitin_0 @ X12 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X10 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( zip_tseitin_0 @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( sk_D @ ( k1_connsp_2 @ X10 @ X9 ) @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v2_tops_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_tops_2 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('62',plain,(
    m1_subset_1 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    zip_tseitin_0 @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_pre_topc @ X5 @ X6 )
      | ~ ( zip_tseitin_0 @ X5 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('67',plain,(
    v4_pre_topc @ ( sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['39','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KXqMWd3l24
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:28:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 34 iterations in 0.024s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.48  thf(t32_connsp_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( v4_pre_topc @ ( k1_connsp_2 @ A @ B ) @ A ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48              ( v4_pre_topc @ ( k1_connsp_2 @ A @ B ) @ A ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t32_connsp_2])).
% 0.21/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k1_connsp_2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( m1_subset_1 @
% 0.21/0.48         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X14)
% 0.21/0.48          | ~ (v2_pre_topc @ X14)
% 0.21/0.48          | (v2_struct_0 @ X14)
% 0.21/0.48          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.21/0.48          | (m1_subset_1 @ (k1_connsp_2 @ X14 @ X15) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.48  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(d7_connsp_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48               ( ( ( C ) = ( k1_connsp_2 @ A @ B ) ) <=>
% 0.21/0.48                 ( ?[D:$i]:
% 0.21/0.48                   ( ( m1_subset_1 @
% 0.21/0.48                       D @ 
% 0.21/0.48                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) & 
% 0.21/0.48                     ( ![E:$i]:
% 0.21/0.48                       ( ( m1_subset_1 @
% 0.21/0.48                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.48                           ( ( r2_hidden @ B @ E ) & ( v4_pre_topc @ E @ A ) & 
% 0.21/0.48                             ( v3_pre_topc @ E @ A ) ) ) ) ) & 
% 0.21/0.48                     ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ D ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_2, axiom,
% 0.21/0.48    (![E:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_0 @ E @ B @ A ) <=>
% 0.21/0.48       ( ( v3_pre_topc @ E @ A ) & ( v4_pre_topc @ E @ A ) & 
% 0.21/0.48         ( r2_hidden @ B @ E ) ) ))).
% 0.21/0.48  thf(zf_stmt_3, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48               ( ( ( C ) = ( k1_connsp_2 @ A @ B ) ) <=>
% 0.21/0.48                 ( ?[D:$i]:
% 0.21/0.48                   ( ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ D ) = ( C ) ) & 
% 0.21/0.48                     ( ![E:$i]:
% 0.21/0.48                       ( ( m1_subset_1 @
% 0.21/0.48                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.48                           ( zip_tseitin_0 @ E @ B @ A ) ) ) ) & 
% 0.21/0.48                     ( m1_subset_1 @
% 0.21/0.48                       D @ 
% 0.21/0.48                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.48          | ((X11) != (k1_connsp_2 @ X10 @ X9))
% 0.21/0.48          | (m1_subset_1 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.48          | ~ (l1_pre_topc @ X10)
% 0.21/0.48          | ~ (v2_pre_topc @ X10)
% 0.21/0.48          | (v2_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X10)
% 0.21/0.48          | ~ (v2_pre_topc @ X10)
% 0.21/0.48          | ~ (l1_pre_topc @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ (k1_connsp_2 @ X10 @ X9) @ 
% 0.21/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.48          | (m1_subset_1 @ (sk_D @ (k1_connsp_2 @ X10 @ X9) @ X9 @ X10) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | (m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.48  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.48  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf(d2_tops_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @
% 0.21/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48           ( ( v2_tops_2 @ B @ A ) <=>
% 0.21/0.48             ( ![C:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.48          | ~ (v4_pre_topc @ (sk_C @ X0 @ X1) @ X1)
% 0.21/0.48          | (v2_tops_2 @ X0 @ X1)
% 0.21/0.48          | ~ (l1_pre_topc @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48           sk_A)
% 0.21/0.48        | ~ (v4_pre_topc @ 
% 0.21/0.48             (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48             sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.48        | ~ (v4_pre_topc @ 
% 0.21/0.48             (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48             sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf(t29_tops_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @
% 0.21/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48           ( ( v2_tops_2 @ B @ A ) =>
% 0.21/0.48             ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X3 @ 
% 0.21/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4))))
% 0.21/0.48          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X4) @ X3) @ X4)
% 0.21/0.48          | ~ (v2_tops_2 @ X3 @ X4)
% 0.21/0.48          | ~ (l1_pre_topc @ X4)
% 0.21/0.48          | ~ (v2_pre_topc @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t29_tops_2])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ~ (v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48             sk_A)
% 0.21/0.48        | (v4_pre_topc @ 
% 0.21/0.48           (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.48            (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)) @ 
% 0.21/0.48           sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.48          | ((X11) != (k1_connsp_2 @ X10 @ X9))
% 0.21/0.48          | ((k6_setfam_1 @ (u1_struct_0 @ X10) @ (sk_D @ X11 @ X9 @ X10))
% 0.21/0.48              = (X11))
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.48          | ~ (l1_pre_topc @ X10)
% 0.21/0.48          | ~ (v2_pre_topc @ X10)
% 0.21/0.48          | (v2_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X10)
% 0.21/0.48          | ~ (v2_pre_topc @ X10)
% 0.21/0.48          | ~ (l1_pre_topc @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ (k1_connsp_2 @ X10 @ X9) @ 
% 0.21/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.48          | ((k6_setfam_1 @ (u1_struct_0 @ X10) @ 
% 0.21/0.48              (sk_D @ (k1_connsp_2 @ X10 @ X9) @ X9 @ X10))
% 0.21/0.48              = (k1_connsp_2 @ X10 @ X9))
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | ((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.48            (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.48            = (k1_connsp_2 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '28'])).
% 0.21/0.48  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.48          (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.48          = (k1_connsp_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.21/0.48  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.48         (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.48         = (k1_connsp_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((~ (v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48           sk_A)
% 0.21/0.48        | (v4_pre_topc @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24', '25', '35'])).
% 0.21/0.48  thf('37', plain, (~ (v4_pre_topc @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (~ (v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (~ (v4_pre_topc @ 
% 0.21/0.48          (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48          sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['20', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.21/0.48          | (v2_tops_2 @ X0 @ X1)
% 0.21/0.48          | ~ (l1_pre_topc @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48           sk_A)
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48           (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48           (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (~ (v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      ((r2_hidden @ 
% 0.21/0.48        (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48        (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.48          | ((X11) != (k1_connsp_2 @ X10 @ X9))
% 0.21/0.48          | ~ (r2_hidden @ X12 @ (sk_D @ X11 @ X9 @ X10))
% 0.21/0.48          | (zip_tseitin_0 @ X12 @ X9 @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.48          | ~ (l1_pre_topc @ X10)
% 0.21/0.48          | ~ (v2_pre_topc @ X10)
% 0.21/0.48          | (v2_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X10)
% 0.21/0.48          | ~ (v2_pre_topc @ X10)
% 0.21/0.48          | ~ (l1_pre_topc @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ (k1_connsp_2 @ X10 @ X9) @ 
% 0.21/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.48          | (zip_tseitin_0 @ X12 @ X9 @ X10)
% 0.21/0.48          | ~ (r2_hidden @ X12 @ (sk_D @ (k1_connsp_2 @ X10 @ X9) @ X9 @ X10))
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ 
% 0.21/0.48               (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.48          | (zip_tseitin_0 @ X0 @ sk_B @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '49'])).
% 0.21/0.48  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ 
% 0.21/0.48             (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.48          | (zip_tseitin_0 @ X0 @ sk_B @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (m1_subset_1 @ 
% 0.21/0.48             (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | (zip_tseitin_0 @ 
% 0.21/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48           sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.48          | (m1_subset_1 @ (sk_C @ X0 @ X1) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.48          | (v2_tops_2 @ X0 @ X1)
% 0.21/0.48          | ~ (l1_pre_topc @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.48           sk_A)
% 0.21/0.48        | (m1_subset_1 @ 
% 0.21/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.48  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (((v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ 
% 0.21/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      (~ (v2_tops_2 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      ((m1_subset_1 @ 
% 0.21/0.48        (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (zip_tseitin_0 @ 
% 0.21/0.48           (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48           sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['55', '62'])).
% 0.21/0.48  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('65', plain,
% 0.21/0.48      ((zip_tseitin_0 @ 
% 0.21/0.48        (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48        sk_B @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         ((v4_pre_topc @ X5 @ X6) | ~ (zip_tseitin_0 @ X5 @ X7 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      ((v4_pre_topc @ 
% 0.21/0.48        (sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.48        sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.48  thf('68', plain, ($false), inference('demod', [status(thm)], ['39', '67'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
