%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jQDlU0Z5r3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:28 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 183 expanded)
%              Number of leaves         :   41 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  644 (1900 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_tops_2 @ X35 @ X36 )
      | ~ ( r2_hidden @ X37 @ X35 )
      | ( v3_pre_topc @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v1_tops_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_tops_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v3_pre_topc @ X32 @ X33 )
      | ( r2_hidden @ X32 @ ( u1_pre_topc @ X33 ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

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

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ ( u1_pre_topc @ X24 ) )
      | ~ ( zip_tseitin_4 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ~ ( zip_tseitin_4 @ sk_B_2 @ sk_A )
    | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

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

thf('27',plain,(
    ! [X29: $i,X31: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ( zip_tseitin_5 @ X31 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('28',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( zip_tseitin_4 @ X26 @ X27 )
      | ~ ( zip_tseitin_5 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,
    ( ~ ( zip_tseitin_5 @ sk_B_2 @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    zip_tseitin_4 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['26','34'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X34 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r2_hidden @ X32 @ ( u1_pre_topc @ X33 ) )
      | ( v3_pre_topc @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['26','34'])).

thf('46',plain,(
    v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jQDlU0Z5r3
% 0.16/0.37  % Computer   : n016.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:53:04 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 120 iterations in 0.089s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.39/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.39/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.39/0.58  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.39/0.58  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(t26_tops_2, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @
% 0.39/0.58             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58           ( ( v1_tops_2 @ B @ A ) =>
% 0.39/0.58             ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( m1_subset_1 @
% 0.39/0.58                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58              ( ( v1_tops_2 @ B @ A ) =>
% 0.39/0.58                ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t26_tops_2])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (~ (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d3_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X1 : $i, X3 : $i]:
% 0.39/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B_2 @ 
% 0.39/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d1_tops_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @
% 0.39/0.58             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58           ( ( v1_tops_2 @ B @ A ) <=>
% 0.39/0.58             ( ![C:$i]:
% 0.39/0.58               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X35 @ 
% 0.39/0.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36))))
% 0.39/0.58          | ~ (v1_tops_2 @ X35 @ X36)
% 0.39/0.58          | ~ (r2_hidden @ X37 @ X35)
% 0.39/0.58          | (v3_pre_topc @ X37 @ X36)
% 0.39/0.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.39/0.58          | ~ (l1_pre_topc @ X36))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ sk_A)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58          | (v3_pre_topc @ X0 @ sk_A)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.39/0.58          | ~ (v1_tops_2 @ sk_B_2 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('6', plain, ((v1_tops_2 @ sk_B_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58          | (v3_pre_topc @ X0 @ sk_A)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.39/0.58      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B_2 @ 
% 0.39/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t4_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.39/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X4 @ X5)
% 0.39/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.39/0.58          | (m1_subset_1 @ X4 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_2) | (v3_pre_topc @ X0 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['7', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.58          | (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X1 : $i, X3 : $i]:
% 0.39/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.58          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_2) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf(d5_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v3_pre_topc @ B @ A ) <=>
% 0.39/0.58             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X32 : $i, X33 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.39/0.58          | ~ (v3_pre_topc @ X32 @ X33)
% 0.39/0.58          | (r2_hidden @ X32 @ (u1_pre_topc @ X33))
% 0.39/0.58          | ~ (l1_pre_topc @ X33))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.39/0.58          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.39/0.58          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ sk_B_2 @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.39/0.58          | (r1_tarski @ sk_B_2 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.39/0.58          | (r1_tarski @ sk_B_2 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X1 : $i, X3 : $i]:
% 0.39/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.39/0.58        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.58  thf('24', plain, ((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))),
% 0.39/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.39/0.58  thf(d1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ( v2_pre_topc @ A ) <=>
% 0.39/0.58         ( ( ![B:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58               ( ![C:$i]:
% 0.39/0.58                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.39/0.58                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.39/0.58                     ( r2_hidden @
% 0.39/0.58                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.39/0.58                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.39/0.58           ( ![B:$i]:
% 0.39/0.58             ( ( m1_subset_1 @
% 0.39/0.58                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.39/0.58                 ( r2_hidden @
% 0.39/0.58                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.39/0.58                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.39/0.58           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_1, axiom,
% 0.39/0.58    (![B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.39/0.58       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.39/0.58         ( r2_hidden @
% 0.39/0.58           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X23 : $i, X24 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.39/0.58          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X24) @ X23) @ 
% 0.39/0.58             (u1_pre_topc @ X24))
% 0.39/0.58          | ~ (zip_tseitin_4 @ X23 @ X24))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      ((~ (zip_tseitin_4 @ sk_B_2 @ sk_A)
% 0.39/0.58        | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.58           (u1_pre_topc @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_3, axiom,
% 0.39/0.58    (![B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.39/0.58       ( ( m1_subset_1 @
% 0.39/0.58           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.39/0.58  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_6, axiom,
% 0.39/0.58    (![B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.39/0.58       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_8, axiom,
% 0.39/0.58    (![C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.39/0.58       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.39/0.58  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_10, axiom,
% 0.39/0.58    (![C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.39/0.58       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.39/0.58         ( r2_hidden @
% 0.39/0.58           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_12, axiom,
% 0.39/0.58    (![C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.39/0.58       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.39/0.58         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_13, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ( v2_pre_topc @ A ) <=>
% 0.39/0.58         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.39/0.58           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.39/0.58           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X29 : $i, X31 : $i]:
% 0.39/0.58         (~ (v2_pre_topc @ X29)
% 0.39/0.58          | (zip_tseitin_5 @ X31 @ X29)
% 0.39/0.58          | ~ (l1_pre_topc @ X29))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B_2 @ 
% 0.39/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X26 : $i, X27 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X26 @ 
% 0.39/0.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 0.39/0.58          | (zip_tseitin_4 @ X26 @ X27)
% 0.39/0.58          | ~ (zip_tseitin_5 @ X26 @ X27))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      ((~ (zip_tseitin_5 @ sk_B_2 @ sk_A) | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58        | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['27', '30'])).
% 0.39/0.58  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('34', plain, ((zip_tseitin_4 @ sk_B_2 @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      ((r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.58        (u1_pre_topc @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '34'])).
% 0.39/0.58  thf(dt_u1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( m1_subset_1 @
% 0.39/0.58         ( u1_pre_topc @ A ) @ 
% 0.39/0.58         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X34 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (u1_pre_topc @ X34) @ 
% 0.39/0.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))
% 0.39/0.58          | ~ (l1_pre_topc @ X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X4 @ X5)
% 0.39/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.39/0.58          | (m1_subset_1 @ X4 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.58          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['35', '38'])).
% 0.39/0.58  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X32 : $i, X33 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.39/0.58          | ~ (r2_hidden @ X32 @ (u1_pre_topc @ X33))
% 0.39/0.58          | (v3_pre_topc @ X32 @ X33)
% 0.39/0.58          | ~ (l1_pre_topc @ X33))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.39/0.58        | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.58             (u1_pre_topc @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      ((r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.39/0.58        (u1_pre_topc @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '34'])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      ((v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.39/0.58  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
