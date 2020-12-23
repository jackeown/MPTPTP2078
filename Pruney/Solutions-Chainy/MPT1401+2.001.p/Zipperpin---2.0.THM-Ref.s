%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DVQIDt2mPJ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 163 expanded)
%              Number of leaves         :   27 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  820 (3012 expanded)
%              Number of equality atoms :   22 (  84 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t31_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ C @ A )
                  & ( v4_pre_topc @ C @ A )
                  & ( r2_hidden @ B @ C )
                  & ( r1_tarski @ C @ ( k1_connsp_2 @ A @ B ) ) )
               => ( C
                  = ( k1_connsp_2 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_pre_topc @ C @ A )
                    & ( v4_pre_topc @ C @ A )
                    & ( r2_hidden @ B @ C )
                    & ( r1_tarski @ C @ ( k1_connsp_2 @ A @ B ) ) )
                 => ( C
                    = ( k1_connsp_2 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_connsp_2])).

thf('0',plain,(
    r1_tarski @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k1_connsp_2 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_C
 != ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k1_connsp_2 @ X12 @ X11 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X11 @ X12 )
      | ( r2_hidden @ X14 @ ( sk_D @ X13 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X12 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X14 @ ( sk_D @ ( k1_connsp_2 @ X12 @ X11 ) @ X11 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_0 @ X0 @ sk_B @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ sk_B @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( v4_pre_topc @ X7 @ X10 )
      | ~ ( v3_pre_topc @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ sk_C @ X0 )
      | ~ ( v4_pre_topc @ sk_C @ X0 )
      | ( zip_tseitin_0 @ sk_C @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    zip_tseitin_0 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_C @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('33',plain,(
    r1_tarski @ ( k1_setfam_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k1_connsp_2 @ X12 @ X11 ) )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X12 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ X12 @ X11 ) @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k6_setfam_1 @ X4 @ X3 )
        = ( k1_setfam_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('45',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    = ( k1_setfam_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k1_connsp_2 @ X12 @ X11 ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X12 ) @ ( sk_D @ X13 @ X11 @ X12 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( k1_connsp_2 @ X12 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X12 ) @ ( sk_D @ ( k1_connsp_2 @ X12 @ X11 ) @ X11 @ X12 ) )
        = ( k1_connsp_2 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      = ( k1_connsp_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
      = ( k1_connsp_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    = ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_setfam_1 @ ( sk_D @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    = ( k1_connsp_2 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['45','55'])).

thf('57',plain,(
    r1_tarski @ ( k1_connsp_2 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['33','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DVQIDt2mPJ
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 41 iterations in 0.023s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.21/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.47  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(t31_connsp_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ( ( v3_pre_topc @ C @ A ) & ( v4_pre_topc @ C @ A ) & 
% 0.21/0.47                   ( r2_hidden @ B @ C ) & 
% 0.21/0.47                   ( r1_tarski @ C @ ( k1_connsp_2 @ A @ B ) ) ) =>
% 0.21/0.47                 ( ( C ) = ( k1_connsp_2 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                  ( ( ( v3_pre_topc @ C @ A ) & ( v4_pre_topc @ C @ A ) & 
% 0.21/0.47                      ( r2_hidden @ B @ C ) & 
% 0.21/0.47                      ( r1_tarski @ C @ ( k1_connsp_2 @ A @ B ) ) ) =>
% 0.21/0.47                    ( ( C ) = ( k1_connsp_2 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t31_connsp_2])).
% 0.21/0.47  thf('0', plain, ((r1_tarski @ sk_C @ (k1_connsp_2 @ sk_A @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i]:
% 0.21/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((~ (r1_tarski @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.47        | ((k1_connsp_2 @ sk_A @ sk_B) = (sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain, (((sk_C) != (k1_connsp_2 @ sk_A @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain, (~ (r1_tarski @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k1_connsp_2, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X16 : $i, X17 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X16)
% 0.21/0.47          | ~ (v2_pre_topc @ X16)
% 0.21/0.47          | (v2_struct_0 @ X16)
% 0.21/0.47          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.47          | (m1_subset_1 @ (k1_connsp_2 @ X16 @ X17) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.47  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf(d7_connsp_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ( ( C ) = ( k1_connsp_2 @ A @ B ) ) <=>
% 0.21/0.47                 ( ?[D:$i]:
% 0.21/0.47                   ( ( m1_subset_1 @
% 0.21/0.47                       D @ 
% 0.21/0.47                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) & 
% 0.21/0.47                     ( ![E:$i]:
% 0.21/0.47                       ( ( m1_subset_1 @
% 0.21/0.47                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.47                           ( ( r2_hidden @ B @ E ) & ( v4_pre_topc @ E @ A ) & 
% 0.21/0.47                             ( v3_pre_topc @ E @ A ) ) ) ) ) & 
% 0.21/0.47                     ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ D ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_2, axiom,
% 0.21/0.47    (![E:$i,B:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_0 @ E @ B @ A ) <=>
% 0.21/0.47       ( ( v3_pre_topc @ E @ A ) & ( v4_pre_topc @ E @ A ) & 
% 0.21/0.47         ( r2_hidden @ B @ E ) ) ))).
% 0.21/0.47  thf(zf_stmt_3, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ( ( C ) = ( k1_connsp_2 @ A @ B ) ) <=>
% 0.21/0.47                 ( ?[D:$i]:
% 0.21/0.47                   ( ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ D ) = ( C ) ) & 
% 0.21/0.47                     ( ![E:$i]:
% 0.21/0.47                       ( ( m1_subset_1 @
% 0.21/0.47                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.47                           ( zip_tseitin_0 @ E @ B @ A ) ) ) ) & 
% 0.21/0.47                     ( m1_subset_1 @
% 0.21/0.47                       D @ 
% 0.21/0.47                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.47          | ((X13) != (k1_connsp_2 @ X12 @ X11))
% 0.21/0.47          | ~ (zip_tseitin_0 @ X14 @ X11 @ X12)
% 0.21/0.47          | (r2_hidden @ X14 @ (sk_D @ X13 @ X11 @ X12))
% 0.21/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | ~ (l1_pre_topc @ X12)
% 0.21/0.47          | ~ (v2_pre_topc @ X12)
% 0.21/0.47          | (v2_struct_0 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X12)
% 0.21/0.47          | ~ (v2_pre_topc @ X12)
% 0.21/0.47          | ~ (l1_pre_topc @ X12)
% 0.21/0.47          | ~ (m1_subset_1 @ (k1_connsp_2 @ X12 @ X11) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | (r2_hidden @ X14 @ (sk_D @ (k1_connsp_2 @ X12 @ X11) @ X11 @ X12))
% 0.21/0.47          | ~ (zip_tseitin_0 @ X14 @ X11 @ X12)
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | ~ (zip_tseitin_0 @ X0 @ sk_B @ sk_A)
% 0.21/0.47          | (r2_hidden @ X0 @ 
% 0.21/0.47             (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.47  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (zip_tseitin_0 @ X0 @ sk_B @ sk_A)
% 0.21/0.47          | (r2_hidden @ X0 @ 
% 0.21/0.47             (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | (r2_hidden @ sk_C @ 
% 0.21/0.47           (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.47        | ~ (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '20'])).
% 0.21/0.47  thf('22', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         ((zip_tseitin_0 @ X7 @ X9 @ X10)
% 0.21/0.47          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.47          | ~ (v4_pre_topc @ X7 @ X10)
% 0.21/0.47          | ~ (v3_pre_topc @ X7 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v3_pre_topc @ sk_C @ X0)
% 0.21/0.47          | ~ (v4_pre_topc @ sk_C @ X0)
% 0.21/0.47          | (zip_tseitin_0 @ sk_C @ sk_B @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A) | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.47  thf('27', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('28', plain, ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | (r2_hidden @ sk_C @ 
% 0.21/0.47           (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['21', '28'])).
% 0.21/0.47  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      ((r2_hidden @ sk_C @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf(t4_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         ((r1_tarski @ (k1_setfam_1 @ X5) @ X6) | ~ (r2_hidden @ X6 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((r1_tarski @ 
% 0.21/0.47        (k1_setfam_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)) @ 
% 0.21/0.47        sk_C)),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.47          | ((X13) != (k1_connsp_2 @ X12 @ X11))
% 0.21/0.47          | (m1_subset_1 @ (sk_D @ X13 @ X11 @ X12) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.21/0.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | ~ (l1_pre_topc @ X12)
% 0.21/0.47          | ~ (v2_pre_topc @ X12)
% 0.21/0.47          | (v2_struct_0 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X12)
% 0.21/0.47          | ~ (v2_pre_topc @ X12)
% 0.21/0.47          | ~ (l1_pre_topc @ X12)
% 0.21/0.47          | ~ (m1_subset_1 @ (k1_connsp_2 @ X12 @ X11) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | (m1_subset_1 @ (sk_D @ (k1_connsp_2 @ X12 @ X11) @ X11 @ X12) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.47  thf('38', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      (((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.47         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.21/0.47  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      ((m1_subset_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.47  thf(redefinition_k6_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (((k6_setfam_1 @ X4 @ X3) = (k1_setfam_1 @ X3))
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.47         (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.47         = (k1_setfam_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.47          | ((X13) != (k1_connsp_2 @ X12 @ X11))
% 0.21/0.47          | ((k6_setfam_1 @ (u1_struct_0 @ X12) @ (sk_D @ X13 @ X11 @ X12))
% 0.21/0.47              = (X13))
% 0.21/0.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | ~ (l1_pre_topc @ X12)
% 0.21/0.47          | ~ (v2_pre_topc @ X12)
% 0.21/0.47          | (v2_struct_0 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X12)
% 0.21/0.47          | ~ (v2_pre_topc @ X12)
% 0.21/0.47          | ~ (l1_pre_topc @ X12)
% 0.21/0.47          | ~ (m1_subset_1 @ (k1_connsp_2 @ X12 @ X11) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | ((k6_setfam_1 @ (u1_struct_0 @ X12) @ 
% 0.21/0.47              (sk_D @ (k1_connsp_2 @ X12 @ X11) @ X11 @ X12))
% 0.21/0.47              = (k1_connsp_2 @ X12 @ X11))
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | ((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.47            (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.47            = (k1_connsp_2 @ sk_A @ sk_B))
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['46', '48'])).
% 0.21/0.47  thf('50', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      ((((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.47          (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.47          = (k1_connsp_2 @ sk_A @ sk_B))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.21/0.47  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('55', plain,
% 0.21/0.47      (((k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.47         (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.47         = (k1_connsp_2 @ sk_A @ sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.47  thf('56', plain,
% 0.21/0.47      (((k1_setfam_1 @ (sk_D @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.21/0.47         = (k1_connsp_2 @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup+', [status(thm)], ['45', '55'])).
% 0.21/0.47  thf('57', plain, ((r1_tarski @ (k1_connsp_2 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['33', '56'])).
% 0.21/0.47  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
