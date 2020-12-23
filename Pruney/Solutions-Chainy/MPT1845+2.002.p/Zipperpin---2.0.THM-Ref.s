%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tVGVYP6Ybr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:53 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  174 (1451 expanded)
%              Number of leaves         :   39 ( 432 expanded)
%              Depth                    :   31
%              Number of atoms          : 1357 (17805 expanded)
%              Number of equality atoms :   35 (1034 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ~ ( v2_pre_topc @ X22 )
      | ( r2_hidden @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(t12_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v2_pre_topc @ A ) )
           => ( v2_pre_topc @ B ) ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v2_pre_topc @ A ) )
             => ( v2_pre_topc @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tex_2])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X25 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( ( g1_pre_topc @ X28 @ X29 )
       != ( g1_pre_topc @ X26 @ X27 ) )
      | ( X29 = X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_2 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_2 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('9',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) )
      | ~ ( zip_tseitin_5 @ ( sk_B_1 @ X22 ) @ X22 )
      | ~ ( zip_tseitin_3 @ ( sk_B @ X22 ) @ X22 )
      | ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('10',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('12',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X25 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( ( g1_pre_topc @ X28 @ X29 )
       != ( g1_pre_topc @ X26 @ X27 ) )
      | ( X28 = X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_2 )
        = X1 )
      | ~ ( l1_pre_topc @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_2 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['12','20'])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('25',plain,
    ( ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ( v2_pre_topc @ sk_B_2 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('27',plain,
    ( ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('29',plain,(
    ! [X19: $i,X21: $i] :
      ( ( zip_tseitin_5 @ X19 @ X21 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( zip_tseitin_5 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ( zip_tseitin_4 @ X19 @ X20 )
      | ~ ( zip_tseitin_5 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_5 @ X0 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('34',plain,(
    ! [X22: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X22 )
      | ( zip_tseitin_5 @ X24 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('37',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( zip_tseitin_1 @ X4 @ X5 @ X7 )
      | ( zip_tseitin_0 @ X4 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('40',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_2 @ X8 @ X10 @ X11 )
      | ~ ( zip_tseitin_1 @ X8 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i,X15: $i] :
      ( ( zip_tseitin_3 @ X12 @ X15 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X15 @ X12 ) @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ X1 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('47',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ X3 )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X2 @ X1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ ( sk_B_1 @ sk_B_2 ) @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('54',plain,(
    ! [X16: $i,X18: $i] :
      ( ( zip_tseitin_4 @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( u1_pre_topc @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( u1_pre_topc @ X17 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X17 ) @ X16 ) @ ( u1_pre_topc @ X17 ) )
      | ~ ( zip_tseitin_4 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_4 @ X0 @ sk_A )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('59',plain,(
    ! [X16: $i,X18: $i] :
      ( ( zip_tseitin_4 @ X16 @ X18 )
      | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X18 ) @ X16 ) @ ( u1_pre_topc @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_B_2 ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ X0 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( zip_tseitin_4 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    ! [X19: $i,X21: $i] :
      ( ( zip_tseitin_5 @ X19 @ X21 )
      | ~ ( zip_tseitin_4 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ X1 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( u1_pre_topc @ X1 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B_2 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ X3 )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_C @ sk_B_2 @ X0 ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ( zip_tseitin_0 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ sk_A )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ sk_A ) ) ),
    inference(condensation,[status(thm)],['80'])).

thf('82',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X6 ) @ X5 @ X4 ) @ ( u1_pre_topc @ X6 ) )
      | ~ ( zip_tseitin_1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ sk_A )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ X0 ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('86',plain,(
    ! [X12: $i,X15: $i] :
      ( ( zip_tseitin_3 @ X12 @ X15 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( zip_tseitin_2 @ X14 @ X12 @ X13 )
      | ~ ( zip_tseitin_3 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_3 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('91',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_pre_topc @ X22 )
      | ( zip_tseitin_3 @ X23 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('94',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_2 @ X1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,
    ( ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_A )
      | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ ( sk_B_1 @ sk_B_2 ) @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ X0 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['57','62'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_A )
      | ( zip_tseitin_4 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X19: $i,X21: $i] :
      ( ( zip_tseitin_5 @ X19 @ X21 )
      | ~ ( zip_tseitin_4 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_A )
      | ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_A )
      | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('104',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('106',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_2 @ X8 @ X10 @ X11 )
      | ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_2 @ X0 @ X1 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( zip_tseitin_1 @ X8 @ X10 @ X9 )
      | ~ ( zip_tseitin_2 @ X8 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_2 @ X0 @ X2 @ sk_B_2 )
      | ~ ( zip_tseitin_2 @ X0 @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_A )
      | ( zip_tseitin_2 @ X0 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X12: $i,X15: $i] :
      ( ( zip_tseitin_3 @ X12 @ X15 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X15 @ X12 ) @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ sk_A )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ X0 ) ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['83','112'])).

thf('114',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('115',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( zip_tseitin_1 @ X4 @ X5 @ X7 )
      | ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X7 ) @ X5 @ X4 ) @ ( u1_pre_topc @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ X1 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_2 @ X8 @ X10 @ X11 )
      | ~ ( zip_tseitin_1 @ X8 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_2 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X12: $i,X15: $i] :
      ( ( zip_tseitin_3 @ X12 @ X15 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X15 @ X12 ) @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('123',plain,
    ( ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['27','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('127',plain,(
    ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['27','124'])).

thf('128',plain,(
    zip_tseitin_4 @ ( sk_B_1 @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ X0 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['57','62'])).

thf('130',plain,(
    zip_tseitin_4 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X19: $i,X21: $i] :
      ( ( zip_tseitin_5 @ X19 @ X21 )
      | ~ ( zip_tseitin_4 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('132',plain,(
    zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['125','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tVGVYP6Ybr
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:22:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.13/2.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.13/2.31  % Solved by: fo/fo7.sh
% 2.13/2.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.31  % done 2422 iterations in 1.861s
% 2.13/2.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.13/2.31  % SZS output start Refutation
% 2.13/2.31  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 2.13/2.31  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 2.13/2.31  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 2.13/2.31  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.13/2.31  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.13/2.31  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.13/2.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.13/2.31  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 2.13/2.31  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.13/2.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.13/2.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.13/2.31  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 2.13/2.31  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 2.13/2.31  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 2.13/2.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.13/2.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.13/2.31  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.13/2.31  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 2.13/2.31  thf(sk_B_type, type, sk_B: $i > $i).
% 2.13/2.31  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.13/2.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.13/2.31  thf(d1_pre_topc, axiom,
% 2.13/2.31    (![A:$i]:
% 2.13/2.31     ( ( l1_pre_topc @ A ) =>
% 2.13/2.31       ( ( v2_pre_topc @ A ) <=>
% 2.13/2.31         ( ( ![B:$i]:
% 2.13/2.31             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.31               ( ![C:$i]:
% 2.13/2.31                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.31                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 2.13/2.31                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 2.13/2.31                     ( r2_hidden @
% 2.13/2.31                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 2.13/2.31                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 2.13/2.31           ( ![B:$i]:
% 2.13/2.31             ( ( m1_subset_1 @
% 2.13/2.31                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.13/2.31               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 2.13/2.31                 ( r2_hidden @
% 2.13/2.31                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 2.13/2.31                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 2.13/2.31           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 2.13/2.31  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 2.13/2.31  thf(zf_stmt_1, axiom,
% 2.13/2.31    (![B:$i,A:$i]:
% 2.13/2.31     ( ( zip_tseitin_5 @ B @ A ) <=>
% 2.13/2.31       ( ( m1_subset_1 @
% 2.13/2.31           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.13/2.31         ( zip_tseitin_4 @ B @ A ) ) ))).
% 2.13/2.31  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 2.13/2.31  thf(zf_stmt_3, axiom,
% 2.13/2.31    (![B:$i,A:$i]:
% 2.13/2.31     ( ( zip_tseitin_4 @ B @ A ) <=>
% 2.13/2.31       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 2.13/2.31         ( r2_hidden @
% 2.13/2.31           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 2.13/2.31  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 2.13/2.31  thf(zf_stmt_5, axiom,
% 2.13/2.31    (![B:$i,A:$i]:
% 2.13/2.31     ( ( zip_tseitin_3 @ B @ A ) <=>
% 2.13/2.31       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.31         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 2.13/2.31  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 2.13/2.31  thf(zf_stmt_7, axiom,
% 2.13/2.31    (![C:$i,B:$i,A:$i]:
% 2.13/2.31     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 2.13/2.31       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.31         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 2.13/2.31  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.13/2.31  thf(zf_stmt_9, axiom,
% 2.13/2.31    (![C:$i,B:$i,A:$i]:
% 2.13/2.31     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 2.13/2.31       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 2.13/2.31         ( r2_hidden @
% 2.13/2.31           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 2.13/2.31  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 2.13/2.31  thf(zf_stmt_11, axiom,
% 2.13/2.31    (![C:$i,B:$i,A:$i]:
% 2.13/2.31     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 2.13/2.31       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 2.13/2.31         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 2.13/2.31  thf(zf_stmt_12, axiom,
% 2.13/2.31    (![A:$i]:
% 2.13/2.31     ( ( l1_pre_topc @ A ) =>
% 2.13/2.31       ( ( v2_pre_topc @ A ) <=>
% 2.13/2.31         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 2.13/2.31           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 2.13/2.31           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 2.13/2.31  thf('0', plain,
% 2.13/2.31      (![X22 : $i]:
% 2.13/2.31         (~ (v2_pre_topc @ X22)
% 2.13/2.31          | (r2_hidden @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22))
% 2.13/2.31          | ~ (l1_pre_topc @ X22))),
% 2.13/2.31      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.13/2.31  thf(t12_tex_2, conjecture,
% 2.13/2.31    (![A:$i]:
% 2.13/2.31     ( ( l1_pre_topc @ A ) =>
% 2.13/2.31       ( ![B:$i]:
% 2.13/2.31         ( ( l1_pre_topc @ B ) =>
% 2.13/2.31           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 2.13/2.31                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 2.13/2.31               ( v2_pre_topc @ A ) ) =>
% 2.13/2.31             ( v2_pre_topc @ B ) ) ) ) ))).
% 2.13/2.31  thf(zf_stmt_13, negated_conjecture,
% 2.13/2.31    (~( ![A:$i]:
% 2.13/2.31        ( ( l1_pre_topc @ A ) =>
% 2.13/2.31          ( ![B:$i]:
% 2.13/2.31            ( ( l1_pre_topc @ B ) =>
% 2.13/2.31              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 2.13/2.31                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 2.13/2.31                  ( v2_pre_topc @ A ) ) =>
% 2.13/2.31                ( v2_pre_topc @ B ) ) ) ) ) )),
% 2.13/2.31    inference('cnf.neg', [status(esa)], [t12_tex_2])).
% 2.13/2.31  thf('1', plain,
% 2.13/2.31      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 2.13/2.31         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 2.13/2.31      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.31  thf(dt_u1_pre_topc, axiom,
% 2.13/2.31    (![A:$i]:
% 2.13/2.31     ( ( l1_pre_topc @ A ) =>
% 2.13/2.31       ( m1_subset_1 @
% 2.13/2.31         ( u1_pre_topc @ A ) @ 
% 2.13/2.31         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 2.13/2.31  thf('2', plain,
% 2.13/2.31      (![X25 : $i]:
% 2.13/2.31         ((m1_subset_1 @ (u1_pre_topc @ X25) @ 
% 2.13/2.31           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))
% 2.13/2.31          | ~ (l1_pre_topc @ X25))),
% 2.13/2.31      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 2.13/2.31  thf(free_g1_pre_topc, axiom,
% 2.13/2.31    (![A:$i,B:$i]:
% 2.13/2.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.13/2.31       ( ![C:$i,D:$i]:
% 2.13/2.31         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 2.13/2.31           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 2.13/2.32  thf('3', plain,
% 2.13/2.32      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.13/2.32         (((g1_pre_topc @ X28 @ X29) != (g1_pre_topc @ X26 @ X27))
% 2.13/2.32          | ((X29) = (X27))
% 2.13/2.32          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X28))))),
% 2.13/2.32      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 2.13/2.32  thf('4', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         (~ (l1_pre_topc @ X0)
% 2.13/2.32          | ((u1_pre_topc @ X0) = (X1))
% 2.13/2.32          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 2.13/2.32              != (g1_pre_topc @ X2 @ X1)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['2', '3'])).
% 2.13/2.32  thf('5', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 2.13/2.32            != (g1_pre_topc @ X1 @ X0))
% 2.13/2.32          | ((u1_pre_topc @ sk_B_2) = (X0))
% 2.13/2.32          | ~ (l1_pre_topc @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['1', '4'])).
% 2.13/2.32  thf('6', plain, ((l1_pre_topc @ sk_B_2)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('7', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 2.13/2.32            != (g1_pre_topc @ X1 @ X0))
% 2.13/2.32          | ((u1_pre_topc @ sk_B_2) = (X0)))),
% 2.13/2.32      inference('demod', [status(thm)], ['5', '6'])).
% 2.13/2.32  thf('8', plain, (((u1_pre_topc @ sk_B_2) = (u1_pre_topc @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['7'])).
% 2.13/2.32  thf('9', plain,
% 2.13/2.32      (![X22 : $i]:
% 2.13/2.32         (~ (r2_hidden @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22))
% 2.13/2.32          | ~ (zip_tseitin_5 @ (sk_B_1 @ X22) @ X22)
% 2.13/2.32          | ~ (zip_tseitin_3 @ (sk_B @ X22) @ X22)
% 2.13/2.32          | (v2_pre_topc @ X22)
% 2.13/2.32          | ~ (l1_pre_topc @ X22))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.13/2.32  thf('10', plain,
% 2.13/2.32      ((~ (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 2.13/2.32        | ~ (l1_pre_topc @ sk_B_2)
% 2.13/2.32        | (v2_pre_topc @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['8', '9'])).
% 2.13/2.32  thf('11', plain, ((l1_pre_topc @ sk_B_2)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('12', plain,
% 2.13/2.32      ((~ (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 2.13/2.32        | (v2_pre_topc @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('demod', [status(thm)], ['10', '11'])).
% 2.13/2.32  thf('13', plain,
% 2.13/2.32      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 2.13/2.32         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('14', plain,
% 2.13/2.32      (![X25 : $i]:
% 2.13/2.32         ((m1_subset_1 @ (u1_pre_topc @ X25) @ 
% 2.13/2.32           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))
% 2.13/2.32          | ~ (l1_pre_topc @ X25))),
% 2.13/2.32      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 2.13/2.32  thf('15', plain,
% 2.13/2.32      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.13/2.32         (((g1_pre_topc @ X28 @ X29) != (g1_pre_topc @ X26 @ X27))
% 2.13/2.32          | ((X28) = (X26))
% 2.13/2.32          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X28))))),
% 2.13/2.32      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 2.13/2.32  thf('16', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         (~ (l1_pre_topc @ X0)
% 2.13/2.32          | ((u1_struct_0 @ X0) = (X1))
% 2.13/2.32          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 2.13/2.32              != (g1_pre_topc @ X1 @ X2)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['14', '15'])).
% 2.13/2.32  thf('17', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 2.13/2.32            != (g1_pre_topc @ X1 @ X0))
% 2.13/2.32          | ((u1_struct_0 @ sk_B_2) = (X1))
% 2.13/2.32          | ~ (l1_pre_topc @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['13', '16'])).
% 2.13/2.32  thf('18', plain, ((l1_pre_topc @ sk_B_2)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('19', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 2.13/2.32            != (g1_pre_topc @ X1 @ X0))
% 2.13/2.32          | ((u1_struct_0 @ sk_B_2) = (X1)))),
% 2.13/2.32      inference('demod', [status(thm)], ['17', '18'])).
% 2.13/2.32  thf('20', plain, (((u1_struct_0 @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['19'])).
% 2.13/2.32  thf('21', plain,
% 2.13/2.32      ((~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 2.13/2.32        | (v2_pre_topc @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('demod', [status(thm)], ['12', '20'])).
% 2.13/2.32  thf('22', plain,
% 2.13/2.32      ((~ (l1_pre_topc @ sk_A)
% 2.13/2.32        | ~ (v2_pre_topc @ sk_A)
% 2.13/2.32        | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | (v2_pre_topc @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['0', '21'])).
% 2.13/2.32  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('25', plain,
% 2.13/2.32      ((~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | (v2_pre_topc @ sk_B_2))),
% 2.13/2.32      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.13/2.32  thf('26', plain, (~ (v2_pre_topc @ sk_B_2)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('27', plain,
% 2.13/2.32      ((~ (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('clc', [status(thm)], ['25', '26'])).
% 2.13/2.32  thf('28', plain, (((u1_struct_0 @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['19'])).
% 2.13/2.32  thf('29', plain,
% 2.13/2.32      (![X19 : $i, X21 : $i]:
% 2.13/2.32         ((zip_tseitin_5 @ X19 @ X21)
% 2.13/2.32          | (m1_subset_1 @ X19 @ 
% 2.13/2.32             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.13/2.32  thf('30', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((m1_subset_1 @ X0 @ 
% 2.13/2.32           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.13/2.32          | (zip_tseitin_5 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('sup+', [status(thm)], ['28', '29'])).
% 2.13/2.32  thf('31', plain,
% 2.13/2.32      (![X19 : $i, X20 : $i]:
% 2.13/2.32         (~ (m1_subset_1 @ X19 @ 
% 2.13/2.32             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 2.13/2.32          | (zip_tseitin_4 @ X19 @ X20)
% 2.13/2.32          | ~ (zip_tseitin_5 @ X19 @ X20))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.13/2.32  thf('32', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_5 @ X0 @ sk_B_2)
% 2.13/2.32          | ~ (zip_tseitin_5 @ X0 @ sk_A)
% 2.13/2.32          | (zip_tseitin_4 @ X0 @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['30', '31'])).
% 2.13/2.32  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('34', plain,
% 2.13/2.32      (![X22 : $i, X24 : $i]:
% 2.13/2.32         (~ (v2_pre_topc @ X22)
% 2.13/2.32          | (zip_tseitin_5 @ X24 @ X22)
% 2.13/2.32          | ~ (l1_pre_topc @ X22))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.13/2.32  thf('35', plain,
% 2.13/2.32      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['33', '34'])).
% 2.13/2.32  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('37', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 2.13/2.32      inference('demod', [status(thm)], ['35', '36'])).
% 2.13/2.32  thf('38', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_5 @ X0 @ sk_B_2) | (zip_tseitin_4 @ X0 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['32', '37'])).
% 2.13/2.32  thf('39', plain,
% 2.13/2.32      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.13/2.32         ((zip_tseitin_1 @ X4 @ X5 @ X7) | (zip_tseitin_0 @ X4 @ X5 @ X7))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_9])).
% 2.13/2.32  thf('40', plain,
% 2.13/2.32      (![X8 : $i, X10 : $i, X11 : $i]:
% 2.13/2.32         ((zip_tseitin_2 @ X8 @ X10 @ X11) | ~ (zip_tseitin_1 @ X8 @ X10 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_7])).
% 2.13/2.32  thf('41', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         ((zip_tseitin_0 @ X2 @ X1 @ X0) | (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['39', '40'])).
% 2.13/2.32  thf('42', plain,
% 2.13/2.32      (![X12 : $i, X15 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X12 @ X15)
% 2.13/2.32          | ~ (zip_tseitin_2 @ (sk_C @ X15 @ X12) @ X12 @ X15))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.13/2.32  thf('43', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_0 @ (sk_C @ X0 @ X1) @ X1 @ X0)
% 2.13/2.32          | (zip_tseitin_3 @ X1 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['41', '42'])).
% 2.13/2.32  thf('44', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         ((r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 2.13/2.32          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_11])).
% 2.13/2.32  thf('45', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X1 @ X0) | (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['43', '44'])).
% 2.13/2.32  thf('46', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X1 @ X0) | (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['43', '44'])).
% 2.13/2.32  thf('47', plain,
% 2.13/2.32      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.13/2.32         ((zip_tseitin_0 @ X2 @ X0 @ X3)
% 2.13/2.32          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X3)))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_11])).
% 2.13/2.32  thf('48', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X1 @ X0)
% 2.13/2.32          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X0))
% 2.13/2.32          | (zip_tseitin_0 @ X1 @ X2 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['46', '47'])).
% 2.13/2.32  thf('49', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X1 @ X0)
% 2.13/2.32          | (zip_tseitin_0 @ X2 @ X1 @ X0)
% 2.13/2.32          | (zip_tseitin_3 @ X2 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['45', '48'])).
% 2.13/2.32  thf('50', plain,
% 2.13/2.32      ((~ (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('clc', [status(thm)], ['25', '26'])).
% 2.13/2.32  thf('51', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_0 @ X0 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32          | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['49', '50'])).
% 2.13/2.32  thf('52', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_4 @ (sk_B_1 @ sk_B_2) @ sk_A)
% 2.13/2.32          | (zip_tseitin_0 @ X0 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_3 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['38', '51'])).
% 2.13/2.32  thf('53', plain, (((u1_pre_topc @ sk_B_2) = (u1_pre_topc @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['7'])).
% 2.13/2.32  thf('54', plain,
% 2.13/2.32      (![X16 : $i, X18 : $i]:
% 2.13/2.32         ((zip_tseitin_4 @ X16 @ X18) | (r1_tarski @ X16 @ (u1_pre_topc @ X18)))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.13/2.32  thf('55', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((r1_tarski @ X0 @ (u1_pre_topc @ sk_A))
% 2.13/2.32          | (zip_tseitin_4 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('sup+', [status(thm)], ['53', '54'])).
% 2.13/2.32  thf('56', plain,
% 2.13/2.32      (![X16 : $i, X17 : $i]:
% 2.13/2.32         (~ (r1_tarski @ X16 @ (u1_pre_topc @ X17))
% 2.13/2.32          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X17) @ X16) @ 
% 2.13/2.32             (u1_pre_topc @ X17))
% 2.13/2.32          | ~ (zip_tseitin_4 @ X16 @ X17))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.13/2.32  thf('57', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_4 @ X0 @ sk_B_2)
% 2.13/2.32          | ~ (zip_tseitin_4 @ X0 @ sk_A)
% 2.13/2.32          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 2.13/2.32             (u1_pre_topc @ sk_A)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['55', '56'])).
% 2.13/2.32  thf('58', plain, (((u1_pre_topc @ sk_B_2) = (u1_pre_topc @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['7'])).
% 2.13/2.32  thf('59', plain,
% 2.13/2.32      (![X16 : $i, X18 : $i]:
% 2.13/2.32         ((zip_tseitin_4 @ X16 @ X18)
% 2.13/2.32          | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X18) @ X16) @ 
% 2.13/2.32               (u1_pre_topc @ X18)))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.13/2.32  thf('60', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_B_2) @ X0) @ 
% 2.13/2.32             (u1_pre_topc @ sk_A))
% 2.13/2.32          | (zip_tseitin_4 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['58', '59'])).
% 2.13/2.32  thf('61', plain, (((u1_struct_0 @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['19'])).
% 2.13/2.32  thf('62', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 2.13/2.32             (u1_pre_topc @ sk_A))
% 2.13/2.32          | (zip_tseitin_4 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('demod', [status(thm)], ['60', '61'])).
% 2.13/2.32  thf('63', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (zip_tseitin_4 @ X0 @ sk_A) | (zip_tseitin_4 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('clc', [status(thm)], ['57', '62'])).
% 2.13/2.32  thf('64', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_0 @ X0 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_4 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['52', '63'])).
% 2.13/2.32  thf('65', plain,
% 2.13/2.32      (![X19 : $i, X21 : $i]:
% 2.13/2.32         ((zip_tseitin_5 @ X19 @ X21) | ~ (zip_tseitin_4 @ X19 @ X21))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.13/2.32  thf('66', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_0 @ X0 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['64', '65'])).
% 2.13/2.32  thf('67', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_0 @ X0 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32          | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['49', '50'])).
% 2.13/2.32  thf('68', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_0 @ X0 @ (sk_B @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('clc', [status(thm)], ['66', '67'])).
% 2.13/2.32  thf('69', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         ((r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 2.13/2.32          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_11])).
% 2.13/2.32  thf('70', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (r2_hidden @ (sk_B @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['68', '69'])).
% 2.13/2.32  thf('71', plain, (((u1_pre_topc @ sk_B_2) = (u1_pre_topc @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['7'])).
% 2.13/2.32  thf('72', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (r2_hidden @ (sk_B @ sk_B_2) @ (u1_pre_topc @ sk_A)))),
% 2.13/2.32      inference('demod', [status(thm)], ['70', '71'])).
% 2.13/2.32  thf('73', plain, (((u1_pre_topc @ sk_B_2) = (u1_pre_topc @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['7'])).
% 2.13/2.32  thf('74', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_0 @ (sk_C @ X0 @ X1) @ X1 @ X0)
% 2.13/2.32          | (zip_tseitin_3 @ X1 @ X0))),
% 2.13/2.32      inference('sup-', [status(thm)], ['41', '42'])).
% 2.13/2.32  thf('75', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         ((r2_hidden @ X2 @ (u1_pre_topc @ X1))
% 2.13/2.32          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_11])).
% 2.13/2.32  thf('76', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X1 @ X0)
% 2.13/2.32          | (r2_hidden @ (sk_C @ X0 @ X1) @ (u1_pre_topc @ X0)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['74', '75'])).
% 2.13/2.32  thf('77', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((r2_hidden @ (sk_C @ sk_B_2 @ X0) @ (u1_pre_topc @ sk_A))
% 2.13/2.32          | (zip_tseitin_3 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('sup+', [status(thm)], ['73', '76'])).
% 2.13/2.32  thf('78', plain,
% 2.13/2.32      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.13/2.32         ((zip_tseitin_0 @ X2 @ X0 @ X3)
% 2.13/2.32          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 2.13/2.32          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X3)))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_11])).
% 2.13/2.32  thf('79', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ sk_A))
% 2.13/2.32          | (zip_tseitin_0 @ (sk_C @ sk_B_2 @ X0) @ X1 @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['77', '78'])).
% 2.13/2.32  thf('80', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X1 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_0 @ (sk_C @ sk_B_2 @ X0) @ (sk_B @ sk_B_2) @ sk_A)
% 2.13/2.32          | (zip_tseitin_3 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['72', '79'])).
% 2.13/2.32  thf('81', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_0 @ (sk_C @ sk_B_2 @ X0) @ (sk_B @ sk_B_2) @ sk_A))),
% 2.13/2.32      inference('condensation', [status(thm)], ['80'])).
% 2.13/2.32  thf('82', plain,
% 2.13/2.32      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.13/2.32         (~ (zip_tseitin_0 @ X4 @ X5 @ X6)
% 2.13/2.32          | (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ X6) @ X5 @ X4) @ 
% 2.13/2.32             (u1_pre_topc @ X6))
% 2.13/2.32          | ~ (zip_tseitin_1 @ X4 @ X5 @ X6))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_9])).
% 2.13/2.32  thf('83', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | ~ (zip_tseitin_1 @ (sk_C @ sk_B_2 @ X0) @ (sk_B @ sk_B_2) @ sk_A)
% 2.13/2.32          | (r2_hidden @ 
% 2.13/2.32             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_2) @ 
% 2.13/2.32              (sk_C @ sk_B_2 @ X0)) @ 
% 2.13/2.32             (u1_pre_topc @ sk_A)))),
% 2.13/2.32      inference('sup-', [status(thm)], ['81', '82'])).
% 2.13/2.32  thf('84', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_5 @ X0 @ sk_B_2) | (zip_tseitin_4 @ X0 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['32', '37'])).
% 2.13/2.32  thf('85', plain, (((u1_struct_0 @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['19'])).
% 2.13/2.32  thf('86', plain,
% 2.13/2.32      (![X12 : $i, X15 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X12 @ X15)
% 2.13/2.32          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.13/2.32  thf('87', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.13/2.32          | (zip_tseitin_3 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('sup+', [status(thm)], ['85', '86'])).
% 2.13/2.32  thf('88', plain,
% 2.13/2.32      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.13/2.32         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.13/2.32          | (zip_tseitin_2 @ X14 @ X12 @ X13)
% 2.13/2.32          | ~ (zip_tseitin_3 @ X12 @ X13))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.13/2.32  thf('89', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | ~ (zip_tseitin_3 @ X0 @ sk_A)
% 2.13/2.32          | (zip_tseitin_2 @ X1 @ X0 @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['87', '88'])).
% 2.13/2.32  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('91', plain,
% 2.13/2.32      (![X22 : $i, X23 : $i]:
% 2.13/2.32         (~ (v2_pre_topc @ X22)
% 2.13/2.32          | (zip_tseitin_3 @ X23 @ X22)
% 2.13/2.32          | ~ (l1_pre_topc @ X22))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.13/2.32  thf('92', plain,
% 2.13/2.32      (![X0 : $i]: ((zip_tseitin_3 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['90', '91'])).
% 2.13/2.32  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.13/2.32  thf('94', plain, (![X0 : $i]: (zip_tseitin_3 @ X0 @ sk_A)),
% 2.13/2.32      inference('demod', [status(thm)], ['92', '93'])).
% 2.13/2.32  thf('95', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2) | (zip_tseitin_2 @ X1 @ X0 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['89', '94'])).
% 2.13/2.32  thf('96', plain,
% 2.13/2.32      ((~ (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('clc', [status(thm)], ['25', '26'])).
% 2.13/2.32  thf('97', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_2 @ X0 @ (sk_B @ sk_B_2) @ sk_A)
% 2.13/2.32          | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['95', '96'])).
% 2.13/2.32  thf('98', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_4 @ (sk_B_1 @ sk_B_2) @ sk_A)
% 2.13/2.32          | (zip_tseitin_2 @ X0 @ (sk_B @ sk_B_2) @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['84', '97'])).
% 2.13/2.32  thf('99', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (zip_tseitin_4 @ X0 @ sk_A) | (zip_tseitin_4 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('clc', [status(thm)], ['57', '62'])).
% 2.13/2.32  thf('100', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_2 @ X0 @ (sk_B @ sk_B_2) @ sk_A)
% 2.13/2.32          | (zip_tseitin_4 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['98', '99'])).
% 2.13/2.32  thf('101', plain,
% 2.13/2.32      (![X19 : $i, X21 : $i]:
% 2.13/2.32         ((zip_tseitin_5 @ X19 @ X21) | ~ (zip_tseitin_4 @ X19 @ X21))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.13/2.32  thf('102', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_2 @ X0 @ (sk_B @ sk_B_2) @ sk_A)
% 2.13/2.32          | (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['100', '101'])).
% 2.13/2.32  thf('103', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_2 @ X0 @ (sk_B @ sk_B_2) @ sk_A)
% 2.13/2.32          | ~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['95', '96'])).
% 2.13/2.32  thf('104', plain,
% 2.13/2.32      (![X0 : $i]: (zip_tseitin_2 @ X0 @ (sk_B @ sk_B_2) @ sk_A)),
% 2.13/2.32      inference('clc', [status(thm)], ['102', '103'])).
% 2.13/2.32  thf('105', plain, (((u1_struct_0 @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['19'])).
% 2.13/2.32  thf('106', plain,
% 2.13/2.32      (![X8 : $i, X10 : $i, X11 : $i]:
% 2.13/2.32         ((zip_tseitin_2 @ X8 @ X10 @ X11)
% 2.13/2.32          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_7])).
% 2.13/2.32  thf('107', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.13/2.32          | (zip_tseitin_2 @ X0 @ X1 @ sk_B_2))),
% 2.13/2.32      inference('sup+', [status(thm)], ['105', '106'])).
% 2.13/2.32  thf('108', plain,
% 2.13/2.32      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.13/2.32         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 2.13/2.32          | (zip_tseitin_1 @ X8 @ X10 @ X9)
% 2.13/2.32          | ~ (zip_tseitin_2 @ X8 @ X10 @ X9))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_7])).
% 2.13/2.32  thf('109', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.32         ((zip_tseitin_2 @ X0 @ X2 @ sk_B_2)
% 2.13/2.32          | ~ (zip_tseitin_2 @ X0 @ X1 @ sk_A)
% 2.13/2.32          | (zip_tseitin_1 @ X0 @ X1 @ sk_A))),
% 2.13/2.32      inference('sup-', [status(thm)], ['107', '108'])).
% 2.13/2.32  thf('110', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         ((zip_tseitin_1 @ X0 @ (sk_B @ sk_B_2) @ sk_A)
% 2.13/2.32          | (zip_tseitin_2 @ X0 @ X1 @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['104', '109'])).
% 2.13/2.32  thf('111', plain,
% 2.13/2.32      (![X12 : $i, X15 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X12 @ X15)
% 2.13/2.32          | ~ (zip_tseitin_2 @ (sk_C @ X15 @ X12) @ X12 @ X15))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.13/2.32  thf('112', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_1 @ (sk_C @ sk_B_2 @ X0) @ (sk_B @ sk_B_2) @ sk_A)
% 2.13/2.32          | (zip_tseitin_3 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['110', '111'])).
% 2.13/2.32  thf('113', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((r2_hidden @ 
% 2.13/2.32           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_2) @ 
% 2.13/2.32            (sk_C @ sk_B_2 @ X0)) @ 
% 2.13/2.32           (u1_pre_topc @ sk_A))
% 2.13/2.32          | (zip_tseitin_3 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('clc', [status(thm)], ['83', '112'])).
% 2.13/2.32  thf('114', plain, (((u1_pre_topc @ sk_B_2) = (u1_pre_topc @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['7'])).
% 2.13/2.32  thf('115', plain,
% 2.13/2.32      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.13/2.32         ((zip_tseitin_1 @ X4 @ X5 @ X7)
% 2.13/2.32          | ~ (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ X7) @ X5 @ X4) @ 
% 2.13/2.32               (u1_pre_topc @ X7)))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_9])).
% 2.13/2.32  thf('116', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_B_2) @ X1 @ X0) @ 
% 2.13/2.32             (u1_pre_topc @ sk_A))
% 2.13/2.32          | (zip_tseitin_1 @ X0 @ X1 @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['114', '115'])).
% 2.13/2.32  thf('117', plain, (((u1_struct_0 @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 2.13/2.32      inference('eq_res', [status(thm)], ['19'])).
% 2.13/2.32  thf('118', plain,
% 2.13/2.32      (![X0 : $i, X1 : $i]:
% 2.13/2.32         (~ (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0) @ 
% 2.13/2.32             (u1_pre_topc @ sk_A))
% 2.13/2.32          | (zip_tseitin_1 @ X0 @ X1 @ sk_B_2))),
% 2.13/2.32      inference('demod', [status(thm)], ['116', '117'])).
% 2.13/2.32  thf('119', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_1 @ (sk_C @ sk_B_2 @ X0) @ (sk_B @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['113', '118'])).
% 2.13/2.32  thf('120', plain,
% 2.13/2.32      (![X8 : $i, X10 : $i, X11 : $i]:
% 2.13/2.32         ((zip_tseitin_2 @ X8 @ X10 @ X11) | ~ (zip_tseitin_1 @ X8 @ X10 @ X11))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_7])).
% 2.13/2.32  thf('121', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X0 @ sk_B_2)
% 2.13/2.32          | (zip_tseitin_2 @ (sk_C @ sk_B_2 @ X0) @ (sk_B @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['119', '120'])).
% 2.13/2.32  thf('122', plain,
% 2.13/2.32      (![X12 : $i, X15 : $i]:
% 2.13/2.32         ((zip_tseitin_3 @ X12 @ X15)
% 2.13/2.32          | ~ (zip_tseitin_2 @ (sk_C @ X15 @ X12) @ X12 @ X15))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.13/2.32  thf('123', plain,
% 2.13/2.32      (((zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)
% 2.13/2.32        | (zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2))),
% 2.13/2.32      inference('sup-', [status(thm)], ['121', '122'])).
% 2.13/2.32  thf('124', plain, ((zip_tseitin_3 @ (sk_B @ sk_B_2) @ sk_B_2)),
% 2.13/2.32      inference('simplify', [status(thm)], ['123'])).
% 2.13/2.32  thf('125', plain, (~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2)),
% 2.13/2.32      inference('demod', [status(thm)], ['27', '124'])).
% 2.13/2.32  thf('126', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         ((zip_tseitin_5 @ X0 @ sk_B_2) | (zip_tseitin_4 @ X0 @ sk_A))),
% 2.13/2.32      inference('demod', [status(thm)], ['32', '37'])).
% 2.13/2.32  thf('127', plain, (~ (zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2)),
% 2.13/2.32      inference('demod', [status(thm)], ['27', '124'])).
% 2.13/2.32  thf('128', plain, ((zip_tseitin_4 @ (sk_B_1 @ sk_B_2) @ sk_A)),
% 2.13/2.32      inference('sup-', [status(thm)], ['126', '127'])).
% 2.13/2.32  thf('129', plain,
% 2.13/2.32      (![X0 : $i]:
% 2.13/2.32         (~ (zip_tseitin_4 @ X0 @ sk_A) | (zip_tseitin_4 @ X0 @ sk_B_2))),
% 2.13/2.32      inference('clc', [status(thm)], ['57', '62'])).
% 2.13/2.32  thf('130', plain, ((zip_tseitin_4 @ (sk_B_1 @ sk_B_2) @ sk_B_2)),
% 2.13/2.32      inference('sup-', [status(thm)], ['128', '129'])).
% 2.13/2.32  thf('131', plain,
% 2.13/2.32      (![X19 : $i, X21 : $i]:
% 2.13/2.32         ((zip_tseitin_5 @ X19 @ X21) | ~ (zip_tseitin_4 @ X19 @ X21))),
% 2.13/2.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.13/2.32  thf('132', plain, ((zip_tseitin_5 @ (sk_B_1 @ sk_B_2) @ sk_B_2)),
% 2.13/2.32      inference('sup-', [status(thm)], ['130', '131'])).
% 2.13/2.32  thf('133', plain, ($false), inference('demod', [status(thm)], ['125', '132'])).
% 2.13/2.32  
% 2.13/2.32  % SZS output end Refutation
% 2.13/2.32  
% 2.13/2.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
