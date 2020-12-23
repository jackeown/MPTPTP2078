%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gouxQtz1hl

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:28 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 146 expanded)
%              Number of leaves         :   41 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  863 (1684 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t26_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
           => ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
             => ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r2_hidden @ X30 @ ( u1_pre_topc @ X31 ) )
      | ( v3_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X32 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X31 )
      | ( r2_hidden @ X30 @ ( u1_pre_topc @ X31 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('17',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_tops_2 @ X33 @ X34 )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ( v3_pre_topc @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v1_tops_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_tops_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B_2 )
    | ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X32 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','35'])).

thf('37',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X32 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_pre_topc @ X0 ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( u1_pre_topc @ X22 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ ( u1_pre_topc @ X22 ) )
      | ~ ( zip_tseitin_4 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,
    ( ~ ( zip_tseitin_4 @ sk_B_2 @ sk_A )
    | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(zf_stmt_2,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('47',plain,(
    ! [X27: $i,X29: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ( zip_tseitin_5 @ X29 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('48',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) )
      | ( zip_tseitin_4 @ X24 @ X25 )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,
    ( ~ ( zip_tseitin_5 @ sk_B_2 @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    zip_tseitin_4 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['46','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['8','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gouxQtz1hl
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.63/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.85  % Solved by: fo/fo7.sh
% 0.63/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.85  % done 553 iterations in 0.378s
% 0.63/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.85  % SZS output start Refutation
% 0.63/0.85  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.63/0.85  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.63/0.85  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.63/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.63/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.63/0.85  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.63/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.63/0.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.63/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.63/0.85  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.63/0.85  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.63/0.85  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.63/0.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.63/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.63/0.85  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.63/0.85  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.63/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.85  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.63/0.85  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.63/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.63/0.85  thf(t26_tops_2, conjecture,
% 0.63/0.85    (![A:$i]:
% 0.63/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.85       ( ![B:$i]:
% 0.63/0.85         ( ( m1_subset_1 @
% 0.63/0.85             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.85           ( ( v1_tops_2 @ B @ A ) =>
% 0.63/0.85             ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.63/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.85    (~( ![A:$i]:
% 0.63/0.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.85          ( ![B:$i]:
% 0.63/0.85            ( ( m1_subset_1 @
% 0.63/0.85                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.85              ( ( v1_tops_2 @ B @ A ) =>
% 0.63/0.85                ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.63/0.85    inference('cnf.neg', [status(esa)], [t26_tops_2])).
% 0.63/0.85  thf('0', plain,
% 0.63/0.85      ((m1_subset_1 @ sk_B_2 @ 
% 0.63/0.85        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf(dt_k5_setfam_1, axiom,
% 0.63/0.85    (![A:$i,B:$i]:
% 0.63/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.63/0.85       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.63/0.85  thf('1', plain,
% 0.63/0.85      (![X3 : $i, X4 : $i]:
% 0.63/0.85         ((m1_subset_1 @ (k5_setfam_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.63/0.85          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.63/0.85      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.63/0.85  thf('2', plain,
% 0.63/0.85      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.63/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.63/0.85  thf(d5_pre_topc, axiom,
% 0.63/0.85    (![A:$i]:
% 0.63/0.85     ( ( l1_pre_topc @ A ) =>
% 0.63/0.85       ( ![B:$i]:
% 0.63/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.85           ( ( v3_pre_topc @ B @ A ) <=>
% 0.63/0.85             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.63/0.85  thf('3', plain,
% 0.63/0.85      (![X30 : $i, X31 : $i]:
% 0.63/0.85         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.63/0.85          | ~ (r2_hidden @ X30 @ (u1_pre_topc @ X31))
% 0.63/0.85          | (v3_pre_topc @ X30 @ X31)
% 0.63/0.85          | ~ (l1_pre_topc @ X31))),
% 0.63/0.85      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.63/0.85  thf('4', plain,
% 0.63/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.85        | (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.63/0.85        | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.63/0.85             (u1_pre_topc @ sk_A)))),
% 0.63/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.63/0.85  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('6', plain,
% 0.63/0.85      (((v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.63/0.85        | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.63/0.85             (u1_pre_topc @ sk_A)))),
% 0.63/0.85      inference('demod', [status(thm)], ['4', '5'])).
% 0.63/0.85  thf('7', plain,
% 0.63/0.85      (~ (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('8', plain,
% 0.63/0.85      (~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.63/0.85          (u1_pre_topc @ sk_A))),
% 0.63/0.85      inference('clc', [status(thm)], ['6', '7'])).
% 0.63/0.85  thf('9', plain,
% 0.63/0.85      ((m1_subset_1 @ sk_B_2 @ 
% 0.63/0.85        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf(dt_u1_pre_topc, axiom,
% 0.63/0.85    (![A:$i]:
% 0.63/0.85     ( ( l1_pre_topc @ A ) =>
% 0.63/0.85       ( m1_subset_1 @
% 0.63/0.85         ( u1_pre_topc @ A ) @ 
% 0.63/0.85         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.63/0.85  thf('10', plain,
% 0.63/0.85      (![X32 : $i]:
% 0.63/0.85         ((m1_subset_1 @ (u1_pre_topc @ X32) @ 
% 0.63/0.85           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))
% 0.63/0.85          | ~ (l1_pre_topc @ X32))),
% 0.63/0.85      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.63/0.85  thf(t7_subset_1, axiom,
% 0.63/0.85    (![A:$i,B:$i]:
% 0.63/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.63/0.85       ( ![C:$i]:
% 0.63/0.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.63/0.85           ( ( ![D:$i]:
% 0.63/0.85               ( ( m1_subset_1 @ D @ A ) =>
% 0.63/0.85                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.63/0.85             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.63/0.85  thf('11', plain,
% 0.63/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.63/0.85          | (r1_tarski @ X2 @ X0)
% 0.63/0.85          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 0.63/0.85          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.63/0.85      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.63/0.85  thf('12', plain,
% 0.63/0.85      (![X0 : $i, X1 : $i]:
% 0.63/0.85         (~ (l1_pre_topc @ X0)
% 0.63/0.85          | ~ (m1_subset_1 @ X1 @ 
% 0.63/0.85               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.63/0.85          | (m1_subset_1 @ 
% 0.63/0.85             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.63/0.85              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.63/0.85             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.63/0.85          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.63/0.85      inference('sup-', [status(thm)], ['10', '11'])).
% 0.63/0.85  thf('13', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | (m1_subset_1 @ 
% 0.63/0.85           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.63/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.63/0.85      inference('sup-', [status(thm)], ['9', '12'])).
% 0.63/0.85  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('15', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | (m1_subset_1 @ 
% 0.63/0.85           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.85      inference('demod', [status(thm)], ['13', '14'])).
% 0.63/0.85  thf('16', plain,
% 0.63/0.85      (![X30 : $i, X31 : $i]:
% 0.63/0.85         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.63/0.85          | ~ (v3_pre_topc @ X30 @ X31)
% 0.63/0.85          | (r2_hidden @ X30 @ (u1_pre_topc @ X31))
% 0.63/0.85          | ~ (l1_pre_topc @ X31))),
% 0.63/0.85      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.63/0.85  thf('17', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.85        | (r2_hidden @ 
% 0.63/0.85           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85           (u1_pre_topc @ sk_A))
% 0.63/0.85        | ~ (v3_pre_topc @ 
% 0.63/0.85             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85             sk_A))),
% 0.63/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.63/0.85  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('19', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | (r2_hidden @ 
% 0.63/0.85           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85           (u1_pre_topc @ sk_A))
% 0.63/0.85        | ~ (v3_pre_topc @ 
% 0.63/0.85             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85             sk_A))),
% 0.63/0.85      inference('demod', [status(thm)], ['17', '18'])).
% 0.63/0.85  thf('20', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | (m1_subset_1 @ 
% 0.63/0.85           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.85      inference('demod', [status(thm)], ['13', '14'])).
% 0.63/0.85  thf('21', plain,
% 0.63/0.85      ((m1_subset_1 @ sk_B_2 @ 
% 0.63/0.85        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf(d1_tops_2, axiom,
% 0.63/0.85    (![A:$i]:
% 0.63/0.85     ( ( l1_pre_topc @ A ) =>
% 0.63/0.85       ( ![B:$i]:
% 0.63/0.85         ( ( m1_subset_1 @
% 0.63/0.85             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.85           ( ( v1_tops_2 @ B @ A ) <=>
% 0.63/0.85             ( ![C:$i]:
% 0.63/0.85               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.85                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.63/0.85  thf('22', plain,
% 0.63/0.85      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.63/0.85         (~ (m1_subset_1 @ X33 @ 
% 0.63/0.85             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))
% 0.63/0.85          | ~ (v1_tops_2 @ X33 @ X34)
% 0.63/0.85          | ~ (r2_hidden @ X35 @ X33)
% 0.63/0.85          | (v3_pre_topc @ X35 @ X34)
% 0.63/0.85          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.63/0.85          | ~ (l1_pre_topc @ X34))),
% 0.63/0.85      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.63/0.85  thf('23', plain,
% 0.63/0.85      (![X0 : $i]:
% 0.63/0.85         (~ (l1_pre_topc @ sk_A)
% 0.63/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.63/0.85          | (v3_pre_topc @ X0 @ sk_A)
% 0.63/0.85          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.63/0.85          | ~ (v1_tops_2 @ sk_B_2 @ sk_A))),
% 0.63/0.85      inference('sup-', [status(thm)], ['21', '22'])).
% 0.63/0.85  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('25', plain, ((v1_tops_2 @ sk_B_2 @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('26', plain,
% 0.63/0.85      (![X0 : $i]:
% 0.63/0.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.63/0.85          | (v3_pre_topc @ X0 @ sk_A)
% 0.63/0.85          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.63/0.85      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.63/0.85  thf('27', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | ~ (r2_hidden @ 
% 0.63/0.85             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85             sk_B_2)
% 0.63/0.85        | (v3_pre_topc @ 
% 0.63/0.85           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85           sk_A))),
% 0.63/0.85      inference('sup-', [status(thm)], ['20', '26'])).
% 0.63/0.85  thf('28', plain,
% 0.63/0.85      ((m1_subset_1 @ sk_B_2 @ 
% 0.63/0.85        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('29', plain,
% 0.63/0.85      (![X32 : $i]:
% 0.63/0.85         ((m1_subset_1 @ (u1_pre_topc @ X32) @ 
% 0.63/0.85           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))
% 0.63/0.85          | ~ (l1_pre_topc @ X32))),
% 0.63/0.85      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.63/0.85  thf('30', plain,
% 0.63/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.63/0.85          | (r1_tarski @ X2 @ X0)
% 0.63/0.85          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 0.63/0.85          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.63/0.85      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.63/0.85  thf('31', plain,
% 0.63/0.85      (![X0 : $i, X1 : $i]:
% 0.63/0.85         (~ (l1_pre_topc @ X0)
% 0.63/0.85          | ~ (m1_subset_1 @ X1 @ 
% 0.63/0.85               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.63/0.85          | (r2_hidden @ 
% 0.63/0.85             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.63/0.85              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.63/0.85             X1)
% 0.63/0.85          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.63/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.63/0.85  thf('32', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | (r2_hidden @ 
% 0.63/0.85           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85           sk_B_2)
% 0.63/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.63/0.85      inference('sup-', [status(thm)], ['28', '31'])).
% 0.63/0.85  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('34', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | (r2_hidden @ 
% 0.63/0.85           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85           sk_B_2))),
% 0.63/0.85      inference('demod', [status(thm)], ['32', '33'])).
% 0.63/0.85  thf('35', plain,
% 0.63/0.85      (((v3_pre_topc @ 
% 0.63/0.85         (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85         sk_A)
% 0.63/0.85        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.63/0.85      inference('clc', [status(thm)], ['27', '34'])).
% 0.63/0.85  thf('36', plain,
% 0.63/0.85      (((r2_hidden @ 
% 0.63/0.85         (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.63/0.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.63/0.85         (u1_pre_topc @ sk_A))
% 0.63/0.85        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.63/0.85      inference('clc', [status(thm)], ['19', '35'])).
% 0.63/0.85  thf('37', plain,
% 0.63/0.85      (![X32 : $i]:
% 0.63/0.85         ((m1_subset_1 @ (u1_pre_topc @ X32) @ 
% 0.63/0.85           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))
% 0.63/0.85          | ~ (l1_pre_topc @ X32))),
% 0.63/0.85      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.63/0.85  thf('38', plain,
% 0.63/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.63/0.85          | (r1_tarski @ X2 @ X0)
% 0.63/0.85          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.63/0.85          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.63/0.85      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.63/0.85  thf('39', plain,
% 0.63/0.85      (![X0 : $i, X1 : $i]:
% 0.63/0.85         (~ (l1_pre_topc @ X0)
% 0.63/0.85          | ~ (m1_subset_1 @ X1 @ 
% 0.63/0.85               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.63/0.85          | ~ (r2_hidden @ 
% 0.63/0.85               (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.63/0.85                (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.63/0.85               (u1_pre_topc @ X0))
% 0.63/0.85          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.63/0.85      inference('sup-', [status(thm)], ['37', '38'])).
% 0.63/0.85  thf('40', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | ~ (m1_subset_1 @ sk_B_2 @ 
% 0.63/0.85             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.63/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.63/0.85      inference('sup-', [status(thm)], ['36', '39'])).
% 0.63/0.85  thf('41', plain,
% 0.63/0.85      ((m1_subset_1 @ sk_B_2 @ 
% 0.63/0.85        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('43', plain,
% 0.63/0.85      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.63/0.85        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.63/0.85      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.63/0.85  thf('44', plain, ((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))),
% 0.63/0.85      inference('simplify', [status(thm)], ['43'])).
% 0.63/0.85  thf(d1_pre_topc, axiom,
% 0.63/0.85    (![A:$i]:
% 0.63/0.85     ( ( l1_pre_topc @ A ) =>
% 0.63/0.85       ( ( v2_pre_topc @ A ) <=>
% 0.63/0.85         ( ( ![B:$i]:
% 0.63/0.85             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.85               ( ![C:$i]:
% 0.63/0.85                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.85                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.63/0.85                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.63/0.85                     ( r2_hidden @
% 0.63/0.85                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.63/0.85                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.63/0.85           ( ![B:$i]:
% 0.63/0.85             ( ( m1_subset_1 @
% 0.63/0.85                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.85               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.63/0.85                 ( r2_hidden @
% 0.63/0.85                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.63/0.85                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.63/0.85           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.63/0.85  thf(zf_stmt_1, axiom,
% 0.63/0.85    (![B:$i,A:$i]:
% 0.63/0.85     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.63/0.85       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.63/0.85         ( r2_hidden @
% 0.63/0.85           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.63/0.85  thf('45', plain,
% 0.63/0.85      (![X21 : $i, X22 : $i]:
% 0.63/0.85         (~ (r1_tarski @ X21 @ (u1_pre_topc @ X22))
% 0.63/0.85          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X22) @ X21) @ 
% 0.63/0.85             (u1_pre_topc @ X22))
% 0.63/0.85          | ~ (zip_tseitin_4 @ X21 @ X22))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.63/0.85  thf('46', plain,
% 0.63/0.85      ((~ (zip_tseitin_4 @ sk_B_2 @ sk_A)
% 0.63/0.85        | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.63/0.85           (u1_pre_topc @ sk_A)))),
% 0.63/0.85      inference('sup-', [status(thm)], ['44', '45'])).
% 0.63/0.85  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $o).
% 0.63/0.85  thf(zf_stmt_3, axiom,
% 0.63/0.85    (![B:$i,A:$i]:
% 0.63/0.85     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.63/0.85       ( ( m1_subset_1 @
% 0.63/0.85           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.85         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.63/0.85  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.63/0.85  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.63/0.85  thf(zf_stmt_6, axiom,
% 0.63/0.85    (![B:$i,A:$i]:
% 0.63/0.85     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.63/0.85       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.85         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.63/0.85  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.63/0.85  thf(zf_stmt_8, axiom,
% 0.63/0.85    (![C:$i,B:$i,A:$i]:
% 0.63/0.85     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.63/0.85       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.85         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.63/0.85  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.63/0.85  thf(zf_stmt_10, axiom,
% 0.63/0.85    (![C:$i,B:$i,A:$i]:
% 0.63/0.85     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.63/0.85       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.63/0.85         ( r2_hidden @
% 0.63/0.85           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.63/0.85  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.63/0.85  thf(zf_stmt_12, axiom,
% 0.63/0.85    (![C:$i,B:$i,A:$i]:
% 0.63/0.85     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.63/0.85       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.63/0.85         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.63/0.85  thf(zf_stmt_13, axiom,
% 0.63/0.85    (![A:$i]:
% 0.63/0.85     ( ( l1_pre_topc @ A ) =>
% 0.63/0.85       ( ( v2_pre_topc @ A ) <=>
% 0.63/0.85         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.63/0.85           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.63/0.85           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.63/0.85  thf('47', plain,
% 0.63/0.85      (![X27 : $i, X29 : $i]:
% 0.63/0.85         (~ (v2_pre_topc @ X27)
% 0.63/0.85          | (zip_tseitin_5 @ X29 @ X27)
% 0.63/0.85          | ~ (l1_pre_topc @ X27))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.63/0.85  thf('48', plain,
% 0.63/0.85      ((m1_subset_1 @ sk_B_2 @ 
% 0.63/0.85        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('49', plain,
% 0.63/0.85      (![X24 : $i, X25 : $i]:
% 0.63/0.85         (~ (m1_subset_1 @ X24 @ 
% 0.63/0.85             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))
% 0.63/0.85          | (zip_tseitin_4 @ X24 @ X25)
% 0.63/0.85          | ~ (zip_tseitin_5 @ X24 @ X25))),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.63/0.85  thf('50', plain,
% 0.63/0.85      ((~ (zip_tseitin_5 @ sk_B_2 @ sk_A) | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.63/0.85      inference('sup-', [status(thm)], ['48', '49'])).
% 0.63/0.85  thf('51', plain,
% 0.63/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.63/0.85        | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.63/0.85      inference('sup-', [status(thm)], ['47', '50'])).
% 0.63/0.85  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.85  thf('54', plain, ((zip_tseitin_4 @ sk_B_2 @ sk_A)),
% 0.63/0.85      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.63/0.85  thf('55', plain,
% 0.63/0.85      ((r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.63/0.85        (u1_pre_topc @ sk_A))),
% 0.63/0.85      inference('demod', [status(thm)], ['46', '54'])).
% 0.63/0.85  thf('56', plain, ($false), inference('demod', [status(thm)], ['8', '55'])).
% 0.63/0.85  
% 0.63/0.85  % SZS output end Refutation
% 0.63/0.85  
% 0.63/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
