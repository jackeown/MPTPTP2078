%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1845+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xrtzTgGFjw

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:24 EST 2020

% Result     : Theorem 22.54s
% Output     : Refutation 22.54s
% Verified   : 
% Statistics : Number of formulae       :  298 (5012 expanded)
%              Number of leaves         :   45 (1494 expanded)
%              Depth                    :   38
%              Number of atoms          : 2796 (61763 expanded)
%              Number of equality atoms :   84 (3314 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t12_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v2_pre_topc @ A ) )
           => ( v2_pre_topc @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v2_pre_topc @ A ) )
             => ( v2_pre_topc @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tex_2])).

thf('0',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X28 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( g1_pre_topc @ X32 @ X33 )
       != ( g1_pre_topc @ X30 @ X31 ) )
      | ( X33 = X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_2 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_2 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

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

thf('8',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) )
      | ~ ( zip_tseitin_5 @ ( sk_B_1 @ X23 ) @ X23 )
      | ~ ( zip_tseitin_3 @ ( sk_B @ X23 ) @ X23 )
      | ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('9',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('14',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X28 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( g1_pre_topc @ X32 @ X33 )
       != ( g1_pre_topc @ X30 @ X31 ) )
      | ( X32 = X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X32 ) ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
      = ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X28 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X28 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['19','26','27','34','35'])).

thf('37',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('41',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X29: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('44',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('45',plain,(
    ! [X23: $i] :
      ( ~ ( v2_pre_topc @ X23 )
      | ( r2_hidden @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('46',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_2 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ sk_B_2 )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( u1_pre_topc @ sk_B_2 )
      = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('52',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('53',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('55',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('57',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','55','56'])).

thf('58',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['11','42','61'])).

thf('63',plain,(
    ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('66',plain,(
    ! [X17: $i,X19: $i] :
      ( ( zip_tseitin_4 @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( u1_pre_topc @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('69',plain,(
    ! [X20: $i,X22: $i] :
      ( ( zip_tseitin_5 @ X20 @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( zip_tseitin_5 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('72',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ( zip_tseitin_4 @ X20 @ X21 )
      | ~ ( zip_tseitin_5 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( zip_tseitin_5 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( zip_tseitin_4 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X29: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('75',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('77',plain,(
    ! [X23: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X23 )
      | ( zip_tseitin_5 @ X25 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_5 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( zip_tseitin_5 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
      | ~ ( l1_pre_topc @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( zip_tseitin_5 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( zip_tseitin_5 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( zip_tseitin_4 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['73','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( zip_tseitin_4 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( u1_pre_topc @ X18 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ ( u1_pre_topc @ X18 ) )
      | ~ ( zip_tseitin_4 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_4 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ X1 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ X0 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','98'])).

thf('100',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('101',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_5 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['67','103'])).

thf('105',plain,(
    ! [X20: $i,X22: $i] :
      ( ( zip_tseitin_5 @ X20 @ X22 )
      | ~ ( zip_tseitin_4 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('108',plain,(
    ! [X17: $i,X19: $i] :
      ( ( zip_tseitin_4 @ X17 @ X19 )
      | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X19 ) @ X17 ) @ ( u1_pre_topc @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_B_2 ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X20: $i,X22: $i] :
      ( ( zip_tseitin_5 @ X20 @ X22 )
      | ~ ( zip_tseitin_4 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('114',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['64','114'])).

thf('116',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('117',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_2 @ X9 @ X11 @ X12 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('118',plain,(
    ! [X13: $i,X16: $i] :
      ( ( zip_tseitin_3 @ X13 @ X16 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X16 @ X13 ) @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ sk_B_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['116','119'])).

thf('121',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('122',plain,(
    ! [X13: $i,X16: $i] :
      ( ( zip_tseitin_3 @ X13 @ X16 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('125',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( zip_tseitin_2 @ X15 @ X13 @ X14 )
      | ~ ( zip_tseitin_3 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_3 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( zip_tseitin_2 @ X1 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X29: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('128',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('129',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X23 )
      | ( zip_tseitin_3 @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( zip_tseitin_3 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_2 @ X1 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['126','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_2 @ X1 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['123','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('138',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( zip_tseitin_1 @ X9 @ X11 @ X10 )
      | ~ ( zip_tseitin_2 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_2 @ X1 @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( zip_tseitin_1 @ X1 @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_1 @ X1 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_1 @ X1 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X0 ) @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['120','146'])).

thf('148',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('149',plain,(
    ! [X13: $i,X16: $i] :
      ( ( zip_tseitin_3 @ X13 @ X16 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('150',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k3_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ X1 )
        = ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['148','151'])).

thf('153',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('154',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X8 )
      | ( zip_tseitin_0 @ X5 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('155',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_2 @ X9 @ X11 @ X12 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X13: $i,X16: $i] :
      ( ( zip_tseitin_3 @ X13 @ X16 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X16 @ X13 ) @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ X1 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['153','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['153','160'])).

thf('163',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X1 @ X4 )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X0 @ X0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['165'])).

thf('167',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 @ X5 ) @ ( u1_pre_topc @ X7 ) )
      | ~ ( zip_tseitin_1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_1 @ X0 @ X0 @ sk_A )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X0 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X23 )
      | ( zip_tseitin_3 @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_2 @ X9 @ X11 @ X12 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('175',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( zip_tseitin_2 @ X15 @ X13 @ X14 )
      | ~ ( zip_tseitin_3 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_2 @ X1 @ X3 @ X0 )
      | ~ ( zip_tseitin_3 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_2 @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ X0 @ X0 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('180',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( zip_tseitin_1 @ X9 @ X11 @ X10 )
      | ~ ( zip_tseitin_2 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_2 @ X0 @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ X0 @ sk_A )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['168','182'])).

thf('184',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('185',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X8 )
      | ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X8 ) @ X6 @ X5 ) @ ( u1_pre_topc @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ X1 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_1 @ X0 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['183','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('192',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X1 @ X4 )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('193',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X2 @ X1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','193'])).

thf('195',plain,(
    ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['64','114'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 @ X5 ) @ ( u1_pre_topc @ X7 ) )
      | ~ ( zip_tseitin_1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_1 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( sk_B @ sk_B_2 ) @ X0 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('200',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_1 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ X0 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('202',plain,
    ( ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_B @ sk_B_2 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['189','201'])).

thf('203',plain,
    ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_B @ sk_B_2 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['64','114'])).

thf('205',plain,(
    r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_B @ sk_B_2 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X0 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('207',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X1 @ X4 )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_B @ sk_B_2 ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_B @ sk_B_2 ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_B @ sk_B_2 ) ) @ sk_A )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['205','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_B @ sk_B_2 ) @ ( k3_xboole_0 @ ( sk_B @ sk_B_2 ) @ ( sk_B @ sk_B_2 ) ) @ sk_A )
      | ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['152','213'])).

thf('215',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_B_2 ) @ ( k3_xboole_0 @ ( sk_B @ sk_B_2 ) @ ( sk_B @ sk_B_2 ) ) @ sk_A )
    | ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(condensation,[status(thm)],['214'])).

thf('216',plain,(
    ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['64','114'])).

thf('217',plain,(
    zip_tseitin_0 @ ( sk_B @ sk_B_2 ) @ ( k3_xboole_0 @ ( sk_B @ sk_B_2 ) @ ( sk_B @ sk_B_2 ) ) @ sk_A ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( u1_pre_topc @ X2 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('219',plain,(
    r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ X1 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('222',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( u1_pre_topc @ X2 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B_2 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['220','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('227',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X1 @ X4 )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('228',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ( zip_tseitin_0 @ X1 @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_0 @ X2 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['225','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( zip_tseitin_0 @ ( sk_C @ sk_B_2 @ X0 ) @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['224','230'])).

thf('232',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_C @ sk_B_2 @ X0 ) @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['219','233'])).

thf('235',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 @ X5 ) @ ( u1_pre_topc @ X7 ) )
      | ~ ( zip_tseitin_1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( sk_B @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ X0 ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('238',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ X0 ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ X0 ) ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['147','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ X0 ) ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['64','114'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) @ ( sk_C @ sk_B_2 @ X0 ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_2 @ X9 @ X11 @ X12 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_2 @ ( sk_C @ sk_B_2 @ X0 ) @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X13: $i,X16: $i] :
      ( ( zip_tseitin_3 @ X13 @ X16 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X16 @ X13 ) @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('249',plain,
    ( ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    $false ),
    inference(demod,[status(thm)],['115','250'])).


%------------------------------------------------------------------------------
