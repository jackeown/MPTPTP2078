%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A8tW1slTmi

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:28 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 245 expanded)
%              Number of leaves         :   41 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  820 (2946 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X33 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X32 )
      | ( r2_hidden @ X31 @ ( u1_pre_topc @ X32 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_tops_2 @ X34 @ X35 )
      | ~ ( r2_hidden @ X36 @ X34 )
      | ( v3_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v1_tops_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_tops_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X33 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_pre_topc @ X0 ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

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

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( u1_pre_topc @ X23 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ ( u1_pre_topc @ X23 ) )
      | ~ ( zip_tseitin_4 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,
    ( ~ ( zip_tseitin_4 @ sk_B_2 @ sk_A )
    | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

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

thf('37',plain,(
    ! [X28: $i,X30: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ( zip_tseitin_5 @ X30 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('38',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) )
      | ( zip_tseitin_4 @ X25 @ X26 )
      | ~ ( zip_tseitin_5 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,
    ( ~ ( zip_tseitin_5 @ sk_B_2 @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    zip_tseitin_4 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X33 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( r2_hidden @ X31 @ ( u1_pre_topc @ X32 ) )
      | ( v3_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['36','44'])).

thf('56',plain,(
    v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A8tW1slTmi
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 1026 iterations in 0.729s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.99/1.17  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.99/1.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.99/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.17  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.99/1.17  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.99/1.17  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.99/1.17  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.17  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.99/1.17  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.99/1.17  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.99/1.17  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.99/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.99/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.17  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.99/1.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.17  thf(t26_tops_2, conjecture,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @
% 0.99/1.17             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17           ( ( v1_tops_2 @ B @ A ) =>
% 0.99/1.17             ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.17    (~( ![A:$i]:
% 0.99/1.17        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.17          ( ![B:$i]:
% 0.99/1.17            ( ( m1_subset_1 @
% 0.99/1.17                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17              ( ( v1_tops_2 @ B @ A ) =>
% 0.99/1.17                ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t26_tops_2])).
% 0.99/1.17  thf('0', plain,
% 0.99/1.17      (~ (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('1', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_2 @ 
% 0.99/1.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(dt_u1_pre_topc, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( m1_subset_1 @
% 0.99/1.17         ( u1_pre_topc @ A ) @ 
% 0.99/1.17         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.99/1.17  thf('2', plain,
% 0.99/1.17      (![X33 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (u1_pre_topc @ X33) @ 
% 0.99/1.17           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33))))
% 0.99/1.17          | ~ (l1_pre_topc @ X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.99/1.17  thf(t7_subset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17       ( ![C:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.17           ( ( ![D:$i]:
% 0.99/1.17               ( ( m1_subset_1 @ D @ A ) =>
% 0.99/1.17                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.99/1.17             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.99/1.17  thf('3', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.99/1.17          | (r1_tarski @ X2 @ X0)
% 0.99/1.17          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.99/1.17  thf('4', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (m1_subset_1 @ X1 @ 
% 0.99/1.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.99/1.17          | (r2_hidden @ 
% 0.99/1.17             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.99/1.17              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.99/1.17             X1)
% 0.99/1.17          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | (r2_hidden @ 
% 0.99/1.17           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17           sk_B_2)
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['1', '4'])).
% 0.99/1.17  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('7', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | (r2_hidden @ 
% 0.99/1.17           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17           sk_B_2))),
% 0.99/1.17      inference('demod', [status(thm)], ['5', '6'])).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_2 @ 
% 0.99/1.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t4_subset, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.99/1.17       ( m1_subset_1 @ A @ C ) ))).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X3 @ X4)
% 0.99/1.17          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.99/1.17          | (m1_subset_1 @ X3 @ X5))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset])).
% 0.99/1.17  thf('10', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.99/1.17      inference('sup-', [status(thm)], ['8', '9'])).
% 0.99/1.17  thf('11', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | (m1_subset_1 @ 
% 0.99/1.17           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['7', '10'])).
% 0.99/1.17  thf(d5_pre_topc, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( ( v3_pre_topc @ B @ A ) <=>
% 0.99/1.17             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.99/1.17  thf('12', plain,
% 0.99/1.17      (![X31 : $i, X32 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.99/1.17          | ~ (v3_pre_topc @ X31 @ X32)
% 0.99/1.17          | (r2_hidden @ X31 @ (u1_pre_topc @ X32))
% 0.99/1.17          | ~ (l1_pre_topc @ X32))),
% 0.99/1.17      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.99/1.17  thf('13', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | (r2_hidden @ 
% 0.99/1.17           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17           (u1_pre_topc @ sk_A))
% 0.99/1.17        | ~ (v3_pre_topc @ 
% 0.99/1.17             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17             sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['11', '12'])).
% 0.99/1.17  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('15', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | (r2_hidden @ 
% 0.99/1.17           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17           (u1_pre_topc @ sk_A))
% 0.99/1.17        | ~ (v3_pre_topc @ 
% 0.99/1.17             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17             sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.99/1.17  thf('16', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | (r2_hidden @ 
% 0.99/1.17           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17           sk_B_2))),
% 0.99/1.17      inference('demod', [status(thm)], ['5', '6'])).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_2 @ 
% 0.99/1.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(d1_tops_2, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @
% 0.99/1.17             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17           ( ( v1_tops_2 @ B @ A ) <=>
% 0.99/1.17             ( ![C:$i]:
% 0.99/1.17               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.99/1.17  thf('18', plain,
% 0.99/1.17      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X34 @ 
% 0.99/1.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35))))
% 0.99/1.17          | ~ (v1_tops_2 @ X34 @ X35)
% 0.99/1.17          | ~ (r2_hidden @ X36 @ X34)
% 0.99/1.17          | (v3_pre_topc @ X36 @ X35)
% 0.99/1.17          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.99/1.17          | ~ (l1_pre_topc @ X35))),
% 0.99/1.17      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.99/1.17  thf('19', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ sk_A)
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17          | (v3_pre_topc @ X0 @ sk_A)
% 0.99/1.17          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.99/1.17          | ~ (v1_tops_2 @ sk_B_2 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['17', '18'])).
% 0.99/1.17  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('21', plain, ((v1_tops_2 @ sk_B_2 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('22', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17          | (v3_pre_topc @ X0 @ sk_A)
% 0.99/1.17          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.99/1.17      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.99/1.17  thf('23', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.99/1.17      inference('sup-', [status(thm)], ['8', '9'])).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_2) | (v3_pre_topc @ X0 @ sk_A))),
% 0.99/1.17      inference('clc', [status(thm)], ['22', '23'])).
% 0.99/1.17  thf('25', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | (v3_pre_topc @ 
% 0.99/1.17           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17           sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['16', '24'])).
% 0.99/1.17  thf('26', plain,
% 0.99/1.17      (((r2_hidden @ 
% 0.99/1.17         (sk_D @ (u1_pre_topc @ sk_A) @ sk_B_2 @ 
% 0.99/1.17          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.99/1.17         (u1_pre_topc @ sk_A))
% 0.99/1.17        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.99/1.17      inference('clc', [status(thm)], ['15', '25'])).
% 0.99/1.17  thf('27', plain,
% 0.99/1.17      (![X33 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (u1_pre_topc @ X33) @ 
% 0.99/1.17           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33))))
% 0.99/1.17          | ~ (l1_pre_topc @ X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.99/1.17  thf('28', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.99/1.17          | (r1_tarski @ X2 @ X0)
% 0.99/1.17          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.99/1.17          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.99/1.17  thf('29', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (m1_subset_1 @ X1 @ 
% 0.99/1.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.99/1.17          | ~ (r2_hidden @ 
% 0.99/1.17               (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.99/1.17                (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.99/1.17               (u1_pre_topc @ X0))
% 0.99/1.17          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['27', '28'])).
% 0.99/1.17  thf('30', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | ~ (m1_subset_1 @ sk_B_2 @ 
% 0.99/1.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['26', '29'])).
% 0.99/1.17  thf('31', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_2 @ 
% 0.99/1.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('33', plain,
% 0.99/1.17      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.99/1.17  thf('34', plain, ((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))),
% 0.99/1.17      inference('simplify', [status(thm)], ['33'])).
% 0.99/1.17  thf(d1_pre_topc, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ( v2_pre_topc @ A ) <=>
% 0.99/1.17         ( ( ![B:$i]:
% 0.99/1.17             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17               ( ![C:$i]:
% 0.99/1.17                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.99/1.17                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.99/1.17                     ( r2_hidden @
% 0.99/1.17                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.99/1.17                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.99/1.17           ( ![B:$i]:
% 0.99/1.17             ( ( m1_subset_1 @
% 0.99/1.17                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.99/1.17                 ( r2_hidden @
% 0.99/1.17                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.99/1.17                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.99/1.17           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_1, axiom,
% 0.99/1.17    (![B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.99/1.17       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.99/1.17         ( r2_hidden @
% 0.99/1.17           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.99/1.17  thf('35', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i]:
% 0.99/1.17         (~ (r1_tarski @ X22 @ (u1_pre_topc @ X23))
% 0.99/1.17          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X23) @ X22) @ 
% 0.99/1.17             (u1_pre_topc @ X23))
% 0.99/1.17          | ~ (zip_tseitin_4 @ X22 @ X23))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.17  thf('36', plain,
% 0.99/1.17      ((~ (zip_tseitin_4 @ sk_B_2 @ sk_A)
% 0.99/1.17        | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.99/1.17           (u1_pre_topc @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['34', '35'])).
% 0.99/1.17  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_3, axiom,
% 0.99/1.17    (![B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.99/1.17       ( ( m1_subset_1 @
% 0.99/1.17           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.99/1.17  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_6, axiom,
% 0.99/1.17    (![B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.99/1.17       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_8, axiom,
% 0.99/1.17    (![C:$i,B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.99/1.17       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.99/1.17  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_10, axiom,
% 0.99/1.17    (![C:$i,B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.99/1.17       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.99/1.17         ( r2_hidden @
% 0.99/1.17           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_12, axiom,
% 0.99/1.17    (![C:$i,B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.99/1.17       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.99/1.17         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_13, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ( v2_pre_topc @ A ) <=>
% 0.99/1.17         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.99/1.17           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.99/1.17           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.99/1.17  thf('37', plain,
% 0.99/1.17      (![X28 : $i, X30 : $i]:
% 0.99/1.17         (~ (v2_pre_topc @ X28)
% 0.99/1.17          | (zip_tseitin_5 @ X30 @ X28)
% 0.99/1.17          | ~ (l1_pre_topc @ X28))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.99/1.17  thf('38', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_2 @ 
% 0.99/1.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('39', plain,
% 0.99/1.17      (![X25 : $i, X26 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X25 @ 
% 0.99/1.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26))))
% 0.99/1.17          | (zip_tseitin_4 @ X25 @ X26)
% 0.99/1.17          | ~ (zip_tseitin_5 @ X25 @ X26))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.17  thf('40', plain,
% 0.99/1.17      ((~ (zip_tseitin_5 @ sk_B_2 @ sk_A) | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['38', '39'])).
% 0.99/1.17  thf('41', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17        | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['37', '40'])).
% 0.99/1.17  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('44', plain, ((zip_tseitin_4 @ sk_B_2 @ sk_A)),
% 0.99/1.17      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.99/1.17  thf('45', plain,
% 0.99/1.17      ((r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.99/1.17        (u1_pre_topc @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['36', '44'])).
% 0.99/1.17  thf('46', plain,
% 0.99/1.17      (![X33 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (u1_pre_topc @ X33) @ 
% 0.99/1.17           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33))))
% 0.99/1.17          | ~ (l1_pre_topc @ X33))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.99/1.17  thf('47', plain,
% 0.99/1.17      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X3 @ X4)
% 0.99/1.17          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.99/1.17          | (m1_subset_1 @ X3 @ X5))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset])).
% 0.99/1.17  thf('48', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.99/1.17          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['46', '47'])).
% 0.99/1.17  thf('49', plain,
% 0.99/1.17      (((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.99/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.18      inference('sup-', [status(thm)], ['45', '48'])).
% 0.99/1.18  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('51', plain,
% 0.99/1.18      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.99/1.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['49', '50'])).
% 0.99/1.18  thf('52', plain,
% 0.99/1.18      (![X31 : $i, X32 : $i]:
% 0.99/1.18         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.99/1.18          | ~ (r2_hidden @ X31 @ (u1_pre_topc @ X32))
% 0.99/1.18          | (v3_pre_topc @ X31 @ X32)
% 0.99/1.18          | ~ (l1_pre_topc @ X32))),
% 0.99/1.18      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.99/1.18  thf('53', plain,
% 0.99/1.18      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.18        | (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.99/1.18        | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.99/1.18             (u1_pre_topc @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['51', '52'])).
% 0.99/1.18  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('55', plain,
% 0.99/1.18      ((r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.99/1.18        (u1_pre_topc @ sk_A))),
% 0.99/1.18      inference('demod', [status(thm)], ['36', '44'])).
% 0.99/1.18  thf('56', plain,
% 0.99/1.18      ((v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.99/1.18      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.99/1.18  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 0.99/1.18  
% 0.99/1.18  % SZS output end Refutation
% 0.99/1.18  
% 0.99/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
