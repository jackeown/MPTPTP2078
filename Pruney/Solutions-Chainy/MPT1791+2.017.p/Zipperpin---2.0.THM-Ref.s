%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t4i5piphcV

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:47 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 237 expanded)
%              Number of leaves         :   45 (  92 expanded)
%              Depth                    :   21
%              Number of atoms          : 1254 (3128 expanded)
%              Number of equality atoms :   71 ( 158 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(t106_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k6_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tmap_1])).

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X31 )
      | ( r2_hidden @ X30 @ ( u1_pre_topc @ X31 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
          <=> ( ( u1_pre_topc @ A )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X35 @ ( u1_pre_topc @ X36 ) )
      | ( ( u1_pre_topc @ X36 )
        = ( k5_tmap_1 @ X36 @ X35 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k6_tmap_1 @ X34 @ X33 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X34 ) @ ( k5_tmap_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      & ( v3_pre_topc @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

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

thf('32',plain,(
    ! [X27: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ( r2_hidden @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('35',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X35 @ ( u1_pre_topc @ X36 ) )
      | ( ( u1_pre_topc @ X36 )
        = ( k5_tmap_1 @ X36 @ X35 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('42',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('43',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k6_tmap_1 @ X34 @ X33 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X34 ) @ ( k5_tmap_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X38 @ X37 ) )
        = ( k5_tmap_1 @ X38 @ X37 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X38 @ X37 ) )
        = ( k5_tmap_1 @ X38 @ X37 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['56','64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
        = ( u1_pre_topc @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['39','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
        = ( u1_pre_topc @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( u1_pre_topc @ X36 )
       != ( k5_tmap_1 @ X36 @ X35 ) )
      | ( r2_hidden @ X35 @ ( u1_pre_topc @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r2_hidden @ X30 @ ( u1_pre_topc @ X31 ) )
      | ( v3_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,
    ( ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t4i5piphcV
% 0.13/0.37  % Computer   : n001.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:45:15 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 344 iterations in 0.211s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.69  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.45/0.69  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.45/0.69  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.69  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.69  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.45/0.69  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.45/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.45/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.69  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.45/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.69  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.45/0.69  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.69  thf(t106_tmap_1, conjecture,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.69             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.45/0.69               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i]:
% 0.45/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.69            ( l1_pre_topc @ A ) ) =>
% 0.45/0.69          ( ![B:$i]:
% 0.45/0.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69              ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.69                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.45/0.69                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69          != (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (~
% 0.45/0.69       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69          = (k6_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.45/0.69       ~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.69      inference('split', [status(esa)], ['0'])).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69          = (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69        | (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.69      inference('split', [status(esa)], ['2'])).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(d5_pre_topc, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_pre_topc @ A ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.69             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X30 : $i, X31 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.45/0.69          | ~ (v3_pre_topc @ X30 @ X31)
% 0.45/0.69          | (r2_hidden @ X30 @ (u1_pre_topc @ X31))
% 0.45/0.69          | ~ (l1_pre_topc @ X31))),
% 0.45/0.69      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.69        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.45/0.69        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (((r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.45/0.69        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (((r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))
% 0.45/0.69         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['3', '8'])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(t103_tmap_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.45/0.69             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X35 : $i, X36 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.45/0.69          | ~ (r2_hidden @ X35 @ (u1_pre_topc @ X36))
% 0.45/0.69          | ((u1_pre_topc @ X36) = (k5_tmap_1 @ X36 @ X35))
% 0.45/0.69          | ~ (l1_pre_topc @ X36)
% 0.45/0.69          | ~ (v2_pre_topc @ X36)
% 0.45/0.69          | (v2_struct_0 @ X36))),
% 0.45/0.69      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.69        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69        | ~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.69  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69        | ~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.45/0.69  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      ((~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.45/0.69        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.45/0.69      inference('clc', [status(thm)], ['15', '16'])).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_2)))
% 0.45/0.69         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['9', '17'])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(d9_tmap_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69           ( ( k6_tmap_1 @ A @ B ) =
% 0.45/0.69             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X33 : $i, X34 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.45/0.69          | ((k6_tmap_1 @ X34 @ X33)
% 0.45/0.69              = (g1_pre_topc @ (u1_struct_0 @ X34) @ (k5_tmap_1 @ X34 @ X33)))
% 0.45/0.69          | ~ (l1_pre_topc @ X34)
% 0.45/0.69          | ~ (v2_pre_topc @ X34)
% 0.45/0.69          | (v2_struct_0 @ X34))),
% 0.45/0.69      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.69        | ((k6_tmap_1 @ sk_A @ sk_B_2)
% 0.45/0.69            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.69  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | ((k6_tmap_1 @ sk_A @ sk_B_2)
% 0.45/0.69            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.69  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (((k6_tmap_1 @ sk_A @ sk_B_2)
% 0.45/0.69         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.45/0.69      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      ((((k6_tmap_1 @ sk_A @ sk_B_2)
% 0.45/0.69          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.45/0.69         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['18', '26'])).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69          != (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.45/0.69         <= (~
% 0.45/0.69             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('split', [status(esa)], ['0'])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      ((((k6_tmap_1 @ sk_A @ sk_B_2) != (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.45/0.69         <= (~
% 0.45/0.69             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))) & 
% 0.45/0.69             ((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69          = (k6_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.45/0.69       ~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.69      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69          = (k6_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.45/0.69       ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.69      inference('split', [status(esa)], ['2'])).
% 0.45/0.69  thf(d1_pre_topc, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_pre_topc @ A ) =>
% 0.45/0.69       ( ( v2_pre_topc @ A ) <=>
% 0.45/0.69         ( ( ![B:$i]:
% 0.45/0.69             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69               ( ![C:$i]:
% 0.45/0.69                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.69                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.45/0.69                     ( r2_hidden @
% 0.45/0.69                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.45/0.69                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.45/0.69           ( ![B:$i]:
% 0.45/0.69             ( ( m1_subset_1 @
% 0.45/0.69                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.69               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.45/0.69                 ( r2_hidden @
% 0.45/0.69                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.45/0.69                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.45/0.69           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_2, axiom,
% 0.45/0.69    (![B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.45/0.69       ( ( m1_subset_1 @
% 0.45/0.69           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.69         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.45/0.69  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_4, axiom,
% 0.45/0.69    (![B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.45/0.69       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.45/0.69         ( r2_hidden @
% 0.45/0.69           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_6, axiom,
% 0.45/0.69    (![B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.45/0.69       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_8, axiom,
% 0.45/0.69    (![C:$i,B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.45/0.69       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.45/0.69  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_10, axiom,
% 0.45/0.69    (![C:$i,B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.45/0.69       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.45/0.69         ( r2_hidden @
% 0.45/0.69           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_12, axiom,
% 0.45/0.69    (![C:$i,B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.45/0.69       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.69         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_13, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_pre_topc @ A ) =>
% 0.45/0.69       ( ( v2_pre_topc @ A ) <=>
% 0.45/0.69         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.69           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.45/0.69           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X27 : $i]:
% 0.45/0.69         (~ (v2_pre_topc @ X27)
% 0.45/0.69          | (r2_hidden @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27))
% 0.45/0.69          | ~ (l1_pre_topc @ X27))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.45/0.69  thf(dt_k2_subset_1, axiom,
% 0.45/0.69    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.45/0.69  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.69  thf('34', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.45/0.69      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.69  thf('35', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.45/0.69      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X35 : $i, X36 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.45/0.69          | ~ (r2_hidden @ X35 @ (u1_pre_topc @ X36))
% 0.45/0.69          | ((u1_pre_topc @ X36) = (k5_tmap_1 @ X36 @ X35))
% 0.45/0.69          | ~ (l1_pre_topc @ X36)
% 0.45/0.69          | ~ (v2_pre_topc @ X36)
% 0.45/0.69          | (v2_struct_0 @ X36))),
% 0.45/0.69      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.45/0.69          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | (v2_struct_0 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['32', '37'])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ X0)
% 0.45/0.69          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0))),
% 0.45/0.69      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69          = (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('split', [status(esa)], ['2'])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ X0)
% 0.45/0.69          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0))),
% 0.45/0.69      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.69  thf('42', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.45/0.69      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (![X33 : $i, X34 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.45/0.69          | ((k6_tmap_1 @ X34 @ X33)
% 0.45/0.69              = (g1_pre_topc @ (u1_struct_0 @ X34) @ (k5_tmap_1 @ X34 @ X33)))
% 0.45/0.69          | ~ (l1_pre_topc @ X34)
% 0.45/0.69          | ~ (v2_pre_topc @ X34)
% 0.45/0.69          | (v2_struct_0 @ X34))),
% 0.45/0.69      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.45/0.69              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.45/0.69                 (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.45/0.69            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | (v2_struct_0 @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | (v2_struct_0 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['41', '44'])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.45/0.69              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.45/0.69      inference('simplify', [status(thm)], ['45'])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.45/0.69           = (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.69         | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69         | (v2_struct_0 @ sk_A)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['40', '46'])).
% 0.45/0.69  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.45/0.69           = (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69         | (v2_struct_0 @ sk_A)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.45/0.69  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.45/0.69          = (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.69  thf('53', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.45/0.69      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.69  thf(t104_tmap_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.45/0.69             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      (![X37 : $i, X38 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.45/0.69          | ((u1_pre_topc @ (k6_tmap_1 @ X38 @ X37)) = (k5_tmap_1 @ X38 @ X37))
% 0.45/0.69          | ~ (l1_pre_topc @ X38)
% 0.45/0.69          | ~ (v2_pre_topc @ X38)
% 0.45/0.69          | (v2_struct_0 @ X38))),
% 0.45/0.69      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.69  thf('55', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.45/0.69              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69           = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.69         | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69         | (v2_struct_0 @ sk_A)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['52', '55'])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      (![X37 : $i, X38 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.45/0.69          | ((u1_pre_topc @ (k6_tmap_1 @ X38 @ X37)) = (k5_tmap_1 @ X38 @ X37))
% 0.45/0.69          | ~ (l1_pre_topc @ X38)
% 0.45/0.69          | ~ (v2_pre_topc @ X38)
% 0.45/0.69          | (v2_struct_0 @ X38))),
% 0.45/0.69      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.69        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69            = (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.69  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69            = (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.45/0.69      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.45/0.69  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('64', plain,
% 0.45/0.69      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69         = (k5_tmap_1 @ sk_A @ sk_B_2))),
% 0.45/0.69      inference('clc', [status(thm)], ['62', '63'])).
% 0.45/0.69  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (((((k5_tmap_1 @ sk_A @ sk_B_2)
% 0.45/0.69           = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.45/0.69         | (v2_struct_0 @ sk_A)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('demod', [status(thm)], ['56', '64', '65', '66'])).
% 0.45/0.69  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      ((((k5_tmap_1 @ sk_A @ sk_B_2)
% 0.45/0.69          = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('clc', [status(thm)], ['67', '68'])).
% 0.45/0.69  thf('70', plain,
% 0.45/0.69      (((((k5_tmap_1 @ sk_A @ sk_B_2) = (u1_pre_topc @ sk_A))
% 0.45/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.69         | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69         | (v2_struct_0 @ sk_A)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['39', '69'])).
% 0.45/0.69  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('73', plain,
% 0.45/0.69      (((((k5_tmap_1 @ sk_A @ sk_B_2) = (u1_pre_topc @ sk_A))
% 0.45/0.69         | (v2_struct_0 @ sk_A)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.45/0.69  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('75', plain,
% 0.45/0.69      ((((k5_tmap_1 @ sk_A @ sk_B_2) = (u1_pre_topc @ sk_A)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('clc', [status(thm)], ['73', '74'])).
% 0.45/0.69  thf('76', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('77', plain,
% 0.45/0.69      (![X35 : $i, X36 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.45/0.69          | ((u1_pre_topc @ X36) != (k5_tmap_1 @ X36 @ X35))
% 0.45/0.69          | (r2_hidden @ X35 @ (u1_pre_topc @ X36))
% 0.45/0.69          | ~ (l1_pre_topc @ X36)
% 0.45/0.69          | ~ (v2_pre_topc @ X36)
% 0.45/0.69          | (v2_struct_0 @ X36))),
% 0.45/0.69      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.45/0.69  thf('78', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.69        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.45/0.69        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.69  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('81', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.45/0.69        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.45/0.69      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.45/0.69  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('83', plain,
% 0.45/0.69      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_2))
% 0.45/0.69        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.69      inference('clc', [status(thm)], ['81', '82'])).
% 0.45/0.69  thf('84', plain,
% 0.45/0.69      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.45/0.69         | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['75', '83'])).
% 0.45/0.69  thf('85', plain,
% 0.45/0.69      (((r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('simplify', [status(thm)], ['84'])).
% 0.45/0.69  thf('86', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('87', plain,
% 0.45/0.69      (![X30 : $i, X31 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.45/0.69          | ~ (r2_hidden @ X30 @ (u1_pre_topc @ X31))
% 0.45/0.69          | (v3_pre_topc @ X30 @ X31)
% 0.45/0.69          | ~ (l1_pre_topc @ X31))),
% 0.45/0.69      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.69  thf('88', plain,
% 0.45/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.69        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.45/0.69        | ~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['86', '87'])).
% 0.45/0.69  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('90', plain,
% 0.45/0.69      (((v3_pre_topc @ sk_B_2 @ sk_A)
% 0.45/0.69        | ~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['88', '89'])).
% 0.45/0.69  thf('91', plain,
% 0.45/0.69      (((v3_pre_topc @ sk_B_2 @ sk_A))
% 0.45/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['85', '90'])).
% 0.45/0.69  thf('92', plain,
% 0.45/0.69      ((~ (v3_pre_topc @ sk_B_2 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.69      inference('split', [status(esa)], ['0'])).
% 0.45/0.69  thf('93', plain,
% 0.45/0.69      (~
% 0.45/0.69       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.45/0.69          = (k6_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.45/0.69       ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['91', '92'])).
% 0.45/0.69  thf('94', plain, ($false),
% 0.45/0.69      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '93'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
