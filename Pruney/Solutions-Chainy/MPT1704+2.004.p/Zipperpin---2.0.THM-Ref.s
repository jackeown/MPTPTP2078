%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kgP65NTz2b

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:07 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  182 (1266 expanded)
%              Number of leaves         :   51 ( 399 expanded)
%              Depth                    :   20
%              Number of atoms          : 1478 (18922 expanded)
%              Number of equality atoms :   28 ( 538 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t13_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_borsuk_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( C
                    = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                 => ( ( ( v1_borsuk_1 @ B @ A )
                      & ( m1_pre_topc @ B @ A ) )
                  <=> ( ( v1_borsuk_1 @ C @ A )
                      & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_tmap_1])).

thf('0',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ( v1_borsuk_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ( v1_borsuk_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( v1_borsuk_1 @ sk_B_2 @ sk_A )
   <= ( v1_borsuk_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X48 @ X49 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t11_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( X44
       != ( u1_struct_0 @ X42 ) )
      | ~ ( v1_borsuk_1 @ X42 @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X43 )
      | ( v4_pre_topc @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('13',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X42 ) @ X43 )
      | ~ ( v1_borsuk_1 @ X42 @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X43 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_B_2 @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('17',plain,(
    ! [X30: $i] :
      ( ~ ( v2_pre_topc @ X30 )
      | ( r2_hidden @ ( u1_struct_0 @ X30 ) @ ( u1_pre_topc @ X30 ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( r2_hidden @ X33 @ ( u1_pre_topc @ X34 ) )
      | ( v3_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v3_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
      = ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('36',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('37',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_pre_topc @ X37 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) ) ) )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','50','51','52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_B_2 @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','54','55','56'])).

thf('58',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B_2 @ sk_A )
      & ( m1_pre_topc @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','57'])).

thf('59',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v1_borsuk_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X48 @ X49 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('62',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( X44
       != ( u1_struct_0 @ X42 ) )
      | ~ ( v4_pre_topc @ X44 @ X43 )
      | ( v1_borsuk_1 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('66',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( v1_borsuk_1 @ X42 @ X43 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X42 ) @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X43 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['59'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C_1 @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B_2 @ sk_A )
      & ( m1_pre_topc @ sk_B_2 @ sk_A )
      & ( m1_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,
    ( ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('76',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) ) @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('77',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
   <= ( v1_borsuk_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('84',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('85',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X42 ) @ X43 )
      | ~ ( v1_borsuk_1 @ X42 @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X43 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('86',plain,
    ( ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['59'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      & ( m1_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('93',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( v1_borsuk_1 @ X42 @ X43 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X42 ) @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X43 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('94',plain,
    ( ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B_2 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','50','51','52','53'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B_2 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ( v1_borsuk_1 @ sk_B_2 @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C_1 @ sk_A )
      & ( m1_pre_topc @ sk_B_2 @ sk_A )
      & ( m1_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,
    ( ~ ( v1_borsuk_1 @ sk_B_2 @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,
    ( ( v1_borsuk_1 @ sk_B_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','4','74','82','102'])).

thf('104',plain,(
    ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','103'])).

thf('105',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['59'])).

thf('106',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','4','74','82','102','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['105','108'])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','50','51','52','53'])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ( X45
       != ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ~ ( m1_pre_topc @ X45 @ X47 )
      | ( m1_pre_topc @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('112',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ( m1_pre_topc @ X46 @ X47 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) @ X47 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) @ X0 )
      | ( m1_pre_topc @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','50','51','52','53'])).

thf('116',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','50','51','52','53'])).

thf('119',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('120',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','50','51','52','53'])).

thf('122',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('123',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( m1_pre_topc @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['113','116','117','118','119','120','121','122','123','124'])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['104','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kgP65NTz2b
% 0.15/0.38  % Computer   : n016.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 13:10:35 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 495 iterations in 0.208s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.70  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.70  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.45/0.70  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.70  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.70  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.45/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.70  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.45/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.70  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.70  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.45/0.70  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.70  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.45/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.45/0.70  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.45/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.70  thf(t13_tmap_1, conjecture,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.45/0.70           ( ![C:$i]:
% 0.45/0.70             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.45/0.70               ( ( ( C ) =
% 0.45/0.70                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.45/0.70                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.70                   ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i]:
% 0.45/0.70        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.70          ( ![B:$i]:
% 0.45/0.70            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.45/0.70              ( ![C:$i]:
% 0.45/0.70                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.45/0.70                  ( ( ( C ) =
% 0.45/0.70                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.45/0.70                    ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.70                      ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t13_tmap_1])).
% 0.45/0.70  thf('0', plain,
% 0.45/0.70      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.45/0.70        | ~ (v1_borsuk_1 @ sk_C_1 @ sk_A)
% 0.45/0.70        | ~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.45/0.70        | ~ (v1_borsuk_1 @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('1', plain,
% 0.45/0.70      ((~ (m1_pre_topc @ sk_B_2 @ sk_A)) <= (~ ((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['0'])).
% 0.45/0.70  thf('2', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_C_1 @ sk_A) | (v1_borsuk_1 @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_C_1 @ sk_A)) | ((v1_borsuk_1 @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('split', [status(esa)], ['2'])).
% 0.45/0.70  thf('4', plain,
% 0.45/0.70      (~ ((m1_pre_topc @ sk_B_2 @ sk_A)) | ~ ((v1_borsuk_1 @ sk_B_2 @ sk_A)) | 
% 0.45/0.70       ~ ((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v1_borsuk_1 @ sk_C_1 @ sk_A))),
% 0.45/0.70      inference('split', [status(esa)], ['0'])).
% 0.45/0.70  thf('5', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_B_2 @ sk_A)) <= (((v1_borsuk_1 @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['2'])).
% 0.45/0.70  thf('6', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_C_1 @ sk_A) | (m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('7', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['6'])).
% 0.45/0.70  thf(t1_tsep_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.70           ( m1_subset_1 @
% 0.45/0.70             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.70  thf('8', plain,
% 0.45/0.70      (![X48 : $i, X49 : $i]:
% 0.45/0.70         (~ (m1_pre_topc @ X48 @ X49)
% 0.45/0.70          | (m1_subset_1 @ (u1_struct_0 @ X48) @ 
% 0.45/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.45/0.70          | ~ (l1_pre_topc @ X49))),
% 0.45/0.70      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.70  thf('9', plain,
% 0.45/0.70      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.70         | (m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.45/0.70            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.45/0.70         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.70  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('11', plain,
% 0.45/0.70      (((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.45/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.70         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.70  thf(t11_tsep_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.70           ( ![C:$i]:
% 0.45/0.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.70                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.70                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.70  thf('12', plain,
% 0.45/0.70      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.45/0.70         (~ (m1_pre_topc @ X42 @ X43)
% 0.45/0.70          | ((X44) != (u1_struct_0 @ X42))
% 0.45/0.70          | ~ (v1_borsuk_1 @ X42 @ X43)
% 0.45/0.70          | ~ (m1_pre_topc @ X42 @ X43)
% 0.45/0.70          | (v4_pre_topc @ X44 @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.45/0.70          | ~ (l1_pre_topc @ X43)
% 0.45/0.70          | ~ (v2_pre_topc @ X43))),
% 0.45/0.70      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      (![X42 : $i, X43 : $i]:
% 0.45/0.70         (~ (v2_pre_topc @ X43)
% 0.45/0.70          | ~ (l1_pre_topc @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.45/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.45/0.70          | (v4_pre_topc @ (u1_struct_0 @ X42) @ X43)
% 0.45/0.70          | ~ (v1_borsuk_1 @ X42 @ X43)
% 0.45/0.70          | ~ (m1_pre_topc @ X42 @ X43))),
% 0.45/0.70      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.70  thf('14', plain,
% 0.45/0.70      (((~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.45/0.70         | ~ (v1_borsuk_1 @ sk_B_2 @ sk_A)
% 0.45/0.70         | (v4_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.45/0.70         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.70         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['11', '13'])).
% 0.45/0.70  thf('15', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['6'])).
% 0.45/0.70  thf('16', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(d1_pre_topc, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ( v2_pre_topc @ A ) <=>
% 0.45/0.70         ( ( ![B:$i]:
% 0.45/0.70             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70               ( ![C:$i]:
% 0.45/0.70                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.70                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.45/0.70                     ( r2_hidden @
% 0.45/0.70                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.45/0.70                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.45/0.70           ( ![B:$i]:
% 0.45/0.70             ( ( m1_subset_1 @
% 0.45/0.70                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.70               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.45/0.70                 ( r2_hidden @
% 0.45/0.70                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.45/0.70                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.45/0.70           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_2, axiom,
% 0.45/0.70    (![B:$i,A:$i]:
% 0.45/0.70     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.45/0.70       ( ( m1_subset_1 @
% 0.45/0.70           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.70         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.45/0.70  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_4, axiom,
% 0.45/0.70    (![B:$i,A:$i]:
% 0.45/0.70     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.45/0.70       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.45/0.70         ( r2_hidden @
% 0.45/0.70           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_6, axiom,
% 0.45/0.70    (![B:$i,A:$i]:
% 0.45/0.70     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.45/0.70       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_8, axiom,
% 0.45/0.70    (![C:$i,B:$i,A:$i]:
% 0.45/0.70     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.45/0.70       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.45/0.70  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_10, axiom,
% 0.45/0.70    (![C:$i,B:$i,A:$i]:
% 0.45/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.45/0.70       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.45/0.70         ( r2_hidden @
% 0.45/0.70           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_12, axiom,
% 0.45/0.70    (![C:$i,B:$i,A:$i]:
% 0.45/0.70     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.45/0.70       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.70         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_13, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ( v2_pre_topc @ A ) <=>
% 0.45/0.70         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.70           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.45/0.70           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      (![X30 : $i]:
% 0.45/0.70         (~ (v2_pre_topc @ X30)
% 0.45/0.70          | (r2_hidden @ (u1_struct_0 @ X30) @ (u1_pre_topc @ X30))
% 0.45/0.70          | ~ (l1_pre_topc @ X30))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.45/0.70  thf(dt_k2_subset_1, axiom,
% 0.45/0.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.45/0.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.70  thf('19', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.45/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.70  thf('20', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.45/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.70  thf(d5_pre_topc, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.70             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (![X33 : $i, X34 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.45/0.70          | ~ (r2_hidden @ X33 @ (u1_pre_topc @ X34))
% 0.45/0.70          | (v3_pre_topc @ X33 @ X34)
% 0.45/0.70          | ~ (l1_pre_topc @ X34))),
% 0.45/0.70      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.70  thf('22', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_pre_topc @ X0)
% 0.45/0.70          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.70          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.70  thf('23', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_pre_topc @ X0)
% 0.45/0.70          | ~ (v2_pre_topc @ X0)
% 0.45/0.70          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.70          | ~ (l1_pre_topc @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['17', '22'])).
% 0.45/0.70  thf('24', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.70          | ~ (v2_pre_topc @ X0)
% 0.45/0.70          | ~ (l1_pre_topc @ X0))),
% 0.45/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.70  thf('25', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.45/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.70  thf(t60_pre_topc, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.45/0.70             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.45/0.70           ( ( v3_pre_topc @
% 0.45/0.70               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.45/0.70             ( m1_subset_1 @
% 0.45/0.70               B @ 
% 0.45/0.70               ( k1_zfmisc_1 @
% 0.45/0.70                 ( u1_struct_0 @
% 0.45/0.70                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.70  thf('26', plain,
% 0.45/0.70      (![X38 : $i, X39 : $i]:
% 0.45/0.70         (~ (v3_pre_topc @ X39 @ X38)
% 0.45/0.70          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.45/0.70          | (m1_subset_1 @ X39 @ 
% 0.45/0.70             (k1_zfmisc_1 @ 
% 0.45/0.70              (u1_struct_0 @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))))
% 0.45/0.70          | ~ (l1_pre_topc @ X38)
% 0.45/0.70          | ~ (v2_pre_topc @ X38))),
% 0.45/0.70      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.45/0.70  thf('27', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v2_pre_topc @ X0)
% 0.45/0.70          | ~ (l1_pre_topc @ X0)
% 0.45/0.70          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.70             (k1_zfmisc_1 @ 
% 0.45/0.70              (u1_struct_0 @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.45/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.70  thf('28', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_pre_topc @ X0)
% 0.45/0.70          | ~ (v2_pre_topc @ X0)
% 0.45/0.70          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.70             (k1_zfmisc_1 @ 
% 0.45/0.70              (u1_struct_0 @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.45/0.70          | ~ (l1_pre_topc @ X0)
% 0.45/0.70          | ~ (v2_pre_topc @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['24', '27'])).
% 0.45/0.70  thf('29', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.70           (k1_zfmisc_1 @ 
% 0.45/0.70            (u1_struct_0 @ 
% 0.45/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.45/0.70          | ~ (v2_pre_topc @ X0)
% 0.45/0.70          | ~ (l1_pre_topc @ X0))),
% 0.45/0.70      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.70  thf(t3_subset, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.70  thf('30', plain,
% 0.45/0.70      (![X5 : $i, X6 : $i]:
% 0.45/0.70         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.70  thf('31', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_pre_topc @ X0)
% 0.45/0.70          | ~ (v2_pre_topc @ X0)
% 0.45/0.70          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.45/0.70             (u1_struct_0 @ 
% 0.45/0.70              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.70  thf(d10_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      (![X0 : $i, X2 : $i]:
% 0.45/0.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.70  thf('33', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v2_pre_topc @ X0)
% 0.45/0.70          | ~ (l1_pre_topc @ X0)
% 0.45/0.70          | ~ (r1_tarski @ 
% 0.45/0.70               (u1_struct_0 @ 
% 0.45/0.70                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.45/0.70               (u1_struct_0 @ X0))
% 0.45/0.70          | ((u1_struct_0 @ 
% 0.45/0.70              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.70              = (u1_struct_0 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.70  thf('34', plain,
% 0.45/0.70      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))
% 0.45/0.70        | ((u1_struct_0 @ 
% 0.45/0.70            (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 0.45/0.70            = (u1_struct_0 @ sk_B_2))
% 0.45/0.70        | ~ (l1_pre_topc @ sk_B_2)
% 0.45/0.70        | ~ (v2_pre_topc @ sk_B_2))),
% 0.45/0.70      inference('sup-', [status(thm)], ['16', '33'])).
% 0.45/0.70  thf('35', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.70          | ~ (v2_pre_topc @ X0)
% 0.45/0.70          | ~ (l1_pre_topc @ X0))),
% 0.45/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.70  thf('36', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.45/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.70  thf('37', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('38', plain,
% 0.45/0.70      (![X37 : $i, X38 : $i]:
% 0.45/0.70         (~ (v3_pre_topc @ X37 @ 
% 0.45/0.70             (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 0.45/0.70          | ~ (m1_subset_1 @ X37 @ 
% 0.45/0.70               (k1_zfmisc_1 @ 
% 0.45/0.70                (u1_struct_0 @ 
% 0.45/0.70                 (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))))
% 0.45/0.70          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.45/0.70          | ~ (l1_pre_topc @ X38)
% 0.45/0.70          | ~ (v2_pre_topc @ X38))),
% 0.45/0.70      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.45/0.70  thf('39', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.45/0.70          | ~ (v2_pre_topc @ sk_B_2)
% 0.45/0.70          | ~ (l1_pre_topc @ sk_B_2)
% 0.45/0.70          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 0.45/0.70          | ~ (v3_pre_topc @ X0 @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.70  thf('40', plain, ((v2_pre_topc @ sk_B_2)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('41', plain, ((l1_pre_topc @ sk_B_2)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('42', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('43', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.45/0.70          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 0.45/0.70          | ~ (v3_pre_topc @ X0 @ sk_C_1))),
% 0.45/0.70      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.45/0.70  thf('44', plain,
% 0.45/0.70      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_C_1)
% 0.45/0.70        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['36', '43'])).
% 0.45/0.70  thf('45', plain,
% 0.45/0.70      ((~ (l1_pre_topc @ sk_C_1)
% 0.45/0.70        | ~ (v2_pre_topc @ sk_C_1)
% 0.45/0.70        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['35', '44'])).
% 0.45/0.70  thf('46', plain, ((l1_pre_topc @ sk_C_1)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('47', plain, ((v2_pre_topc @ sk_C_1)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('48', plain,
% 0.45/0.70      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.45/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))),
% 0.45/0.70      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.45/0.70  thf('49', plain,
% 0.45/0.70      (![X5 : $i, X6 : $i]:
% 0.45/0.70         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.70  thf('50', plain,
% 0.45/0.70      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 0.45/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.70  thf('51', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('52', plain, ((l1_pre_topc @ sk_B_2)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('53', plain, ((v2_pre_topc @ sk_B_2)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('54', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.45/0.70      inference('demod', [status(thm)], ['34', '50', '51', '52', '53'])).
% 0.45/0.70  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('57', plain,
% 0.45/0.70      (((~ (v1_borsuk_1 @ sk_B_2 @ sk_A)
% 0.45/0.70         | (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)))
% 0.45/0.70         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['14', '15', '54', '55', '56'])).
% 0.45/0.70  thf('58', plain,
% 0.45/0.70      (((v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A))
% 0.45/0.70         <= (((v1_borsuk_1 @ sk_B_2 @ sk_A)) & ((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['5', '57'])).
% 0.45/0.70  thf('59', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A) | (v1_borsuk_1 @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('60', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['59'])).
% 0.45/0.70  thf('61', plain,
% 0.45/0.70      (![X48 : $i, X49 : $i]:
% 0.45/0.70         (~ (m1_pre_topc @ X48 @ X49)
% 0.45/0.70          | (m1_subset_1 @ (u1_struct_0 @ X48) @ 
% 0.45/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.45/0.70          | ~ (l1_pre_topc @ X49))),
% 0.45/0.70      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.70  thf('62', plain,
% 0.45/0.70      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.70         | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.45/0.70            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.45/0.70         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.70  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('64', plain,
% 0.45/0.70      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.45/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.70         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.70  thf('65', plain,
% 0.45/0.70      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.45/0.70         (~ (m1_pre_topc @ X42 @ X43)
% 0.45/0.70          | ((X44) != (u1_struct_0 @ X42))
% 0.45/0.70          | ~ (v4_pre_topc @ X44 @ X43)
% 0.45/0.70          | (v1_borsuk_1 @ X42 @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.45/0.70          | ~ (l1_pre_topc @ X43)
% 0.45/0.70          | ~ (v2_pre_topc @ X43))),
% 0.45/0.70      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.45/0.70  thf('66', plain,
% 0.45/0.70      (![X42 : $i, X43 : $i]:
% 0.45/0.70         (~ (v2_pre_topc @ X43)
% 0.45/0.70          | ~ (l1_pre_topc @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.45/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.45/0.70          | (v1_borsuk_1 @ X42 @ X43)
% 0.45/0.70          | ~ (v4_pre_topc @ (u1_struct_0 @ X42) @ X43)
% 0.45/0.70          | ~ (m1_pre_topc @ X42 @ X43))),
% 0.45/0.70      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.70  thf('67', plain,
% 0.45/0.70      (((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.45/0.70         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.45/0.70         | (v1_borsuk_1 @ sk_C_1 @ sk_A)
% 0.45/0.70         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.70         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['64', '66'])).
% 0.45/0.70  thf('68', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['59'])).
% 0.45/0.70  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('71', plain,
% 0.45/0.70      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.45/0.70         | (v1_borsuk_1 @ sk_C_1 @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.45/0.70  thf('72', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_C_1 @ sk_A))
% 0.45/0.70         <= (((v1_borsuk_1 @ sk_B_2 @ sk_A)) & 
% 0.45/0.70             ((m1_pre_topc @ sk_B_2 @ sk_A)) & 
% 0.45/0.70             ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['58', '71'])).
% 0.45/0.70  thf('73', plain,
% 0.45/0.70      ((~ (v1_borsuk_1 @ sk_C_1 @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['0'])).
% 0.45/0.70  thf('74', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_C_1 @ sk_A)) | ~ ((v1_borsuk_1 @ sk_B_2 @ sk_A)) | 
% 0.45/0.70       ~ ((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.70  thf('75', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['6'])).
% 0.45/0.70  thf(t11_tmap_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.70           ( ( v1_pre_topc @
% 0.45/0.70               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.45/0.70             ( m1_pre_topc @
% 0.45/0.70               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.45/0.70  thf('76', plain,
% 0.45/0.70      (![X40 : $i, X41 : $i]:
% 0.45/0.70         (~ (m1_pre_topc @ X40 @ X41)
% 0.45/0.70          | (m1_pre_topc @ 
% 0.45/0.70             (g1_pre_topc @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40)) @ X41)
% 0.45/0.70          | ~ (l1_pre_topc @ X41))),
% 0.45/0.70      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.45/0.70  thf('77', plain,
% 0.45/0.70      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.70         | (m1_pre_topc @ 
% 0.45/0.70            (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)) @ 
% 0.45/0.70            sk_A)))
% 0.45/0.70         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['75', '76'])).
% 0.45/0.70  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('79', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('80', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.45/0.70  thf('81', plain,
% 0.45/0.70      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)) <= (~ ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['0'])).
% 0.45/0.70  thf('82', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['80', '81'])).
% 0.45/0.70  thf('83', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_C_1 @ sk_A)) <= (((v1_borsuk_1 @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['2'])).
% 0.45/0.70  thf('84', plain,
% 0.45/0.70      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.45/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.70         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.70  thf('85', plain,
% 0.45/0.70      (![X42 : $i, X43 : $i]:
% 0.45/0.70         (~ (v2_pre_topc @ X43)
% 0.45/0.70          | ~ (l1_pre_topc @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.45/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.45/0.70          | (v4_pre_topc @ (u1_struct_0 @ X42) @ X43)
% 0.45/0.70          | ~ (v1_borsuk_1 @ X42 @ X43)
% 0.45/0.70          | ~ (m1_pre_topc @ X42 @ X43))),
% 0.45/0.70      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.70  thf('86', plain,
% 0.45/0.70      (((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.45/0.70         | ~ (v1_borsuk_1 @ sk_C_1 @ sk_A)
% 0.45/0.70         | (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.45/0.70         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.70         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.70  thf('87', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['59'])).
% 0.45/0.70  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('90', plain,
% 0.45/0.70      (((~ (v1_borsuk_1 @ sk_C_1 @ sk_A)
% 0.45/0.70         | (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)))
% 0.45/0.70         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.45/0.70  thf('91', plain,
% 0.45/0.70      (((v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A))
% 0.45/0.70         <= (((v1_borsuk_1 @ sk_C_1 @ sk_A)) & ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['83', '90'])).
% 0.45/0.70  thf('92', plain,
% 0.45/0.70      (((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.45/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.70         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.70  thf('93', plain,
% 0.45/0.70      (![X42 : $i, X43 : $i]:
% 0.45/0.70         (~ (v2_pre_topc @ X43)
% 0.45/0.70          | ~ (l1_pre_topc @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.45/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.45/0.70          | (v1_borsuk_1 @ X42 @ X43)
% 0.45/0.70          | ~ (v4_pre_topc @ (u1_struct_0 @ X42) @ X43)
% 0.45/0.70          | ~ (m1_pre_topc @ X42 @ X43))),
% 0.45/0.70      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.70  thf('94', plain,
% 0.45/0.70      (((~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.45/0.70         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.45/0.70         | (v1_borsuk_1 @ sk_B_2 @ sk_A)
% 0.45/0.70         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.70         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['92', '93'])).
% 0.45/0.70  thf('95', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['6'])).
% 0.45/0.70  thf('96', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.45/0.70      inference('demod', [status(thm)], ['34', '50', '51', '52', '53'])).
% 0.45/0.70  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('99', plain,
% 0.45/0.70      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.45/0.70         | (v1_borsuk_1 @ sk_B_2 @ sk_A))) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.45/0.70  thf('100', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_B_2 @ sk_A))
% 0.45/0.70         <= (((v1_borsuk_1 @ sk_C_1 @ sk_A)) & 
% 0.45/0.70             ((m1_pre_topc @ sk_B_2 @ sk_A)) & 
% 0.45/0.70             ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['91', '99'])).
% 0.45/0.70  thf('101', plain,
% 0.45/0.70      ((~ (v1_borsuk_1 @ sk_B_2 @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_B_2 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['0'])).
% 0.45/0.70  thf('102', plain,
% 0.45/0.70      (((v1_borsuk_1 @ sk_B_2 @ sk_A)) | ~ ((m1_pre_topc @ sk_B_2 @ sk_A)) | 
% 0.45/0.70       ~ ((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v1_borsuk_1 @ sk_C_1 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['100', '101'])).
% 0.45/0.70  thf('103', plain, (~ ((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('sat_resolution*', [status(thm)], ['3', '4', '74', '82', '102'])).
% 0.45/0.70  thf('104', plain, (~ (m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.45/0.70      inference('simpl_trail', [status(thm)], ['1', '103'])).
% 0.45/0.70  thf('105', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['59'])).
% 0.45/0.70  thf('106', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A) | (m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('107', plain,
% 0.45/0.70      (((m1_pre_topc @ sk_C_1 @ sk_A)) | ((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('split', [status(esa)], ['106'])).
% 0.45/0.70  thf('108', plain, (((m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.45/0.70      inference('sat_resolution*', [status(thm)],
% 0.45/0.70                ['3', '4', '74', '82', '102', '107'])).
% 0.45/0.70  thf('109', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.45/0.70      inference('simpl_trail', [status(thm)], ['105', '108'])).
% 0.45/0.70  thf('110', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.45/0.70      inference('demod', [status(thm)], ['34', '50', '51', '52', '53'])).
% 0.45/0.70  thf(t12_tmap_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.45/0.70           ( ![C:$i]:
% 0.45/0.70             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.45/0.70               ( ( ( B ) =
% 0.45/0.70                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.45/0.70                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.70  thf('111', plain,
% 0.45/0.70      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.70         (~ (v2_pre_topc @ X45)
% 0.45/0.70          | ~ (l1_pre_topc @ X45)
% 0.45/0.70          | ((X45) != (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 0.45/0.70          | ~ (m1_pre_topc @ X45 @ X47)
% 0.45/0.70          | (m1_pre_topc @ X46 @ X47)
% 0.45/0.70          | ~ (l1_pre_topc @ X46)
% 0.45/0.70          | ~ (v2_pre_topc @ X46)
% 0.45/0.70          | ~ (l1_pre_topc @ X47))),
% 0.45/0.70      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.45/0.70  thf('112', plain,
% 0.45/0.70      (![X46 : $i, X47 : $i]:
% 0.45/0.70         (~ (l1_pre_topc @ X47)
% 0.45/0.70          | ~ (v2_pre_topc @ X46)
% 0.45/0.70          | ~ (l1_pre_topc @ X46)
% 0.45/0.70          | (m1_pre_topc @ X46 @ X47)
% 0.45/0.70          | ~ (m1_pre_topc @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)) @ X47)
% 0.45/0.70          | ~ (l1_pre_topc @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 0.45/0.70          | ~ (v2_pre_topc @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))),
% 0.45/0.70      inference('simplify', [status(thm)], ['111'])).
% 0.45/0.70  thf('113', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_pre_topc @ 
% 0.45/0.70             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B_2)))
% 0.45/0.70          | ~ (v2_pre_topc @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 0.45/0.70          | ~ (m1_pre_topc @ 
% 0.45/0.70               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)) @ 
% 0.45/0.70               X0)
% 0.45/0.70          | (m1_pre_topc @ sk_B_2 @ X0)
% 0.45/0.70          | ~ (l1_pre_topc @ sk_B_2)
% 0.45/0.70          | ~ (v2_pre_topc @ sk_B_2)
% 0.45/0.70          | ~ (l1_pre_topc @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['110', '112'])).
% 0.45/0.70  thf('114', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('115', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.45/0.70      inference('demod', [status(thm)], ['34', '50', '51', '52', '53'])).
% 0.45/0.70  thf('116', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('demod', [status(thm)], ['114', '115'])).
% 0.45/0.70  thf('117', plain, ((l1_pre_topc @ sk_C_1)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('118', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.45/0.70      inference('demod', [status(thm)], ['34', '50', '51', '52', '53'])).
% 0.45/0.70  thf('119', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('demod', [status(thm)], ['114', '115'])).
% 0.45/0.70  thf('120', plain, ((v2_pre_topc @ sk_C_1)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('121', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.45/0.70      inference('demod', [status(thm)], ['34', '50', '51', '52', '53'])).
% 0.45/0.70  thf('122', plain,
% 0.45/0.70      (((sk_C_1)
% 0.45/0.70         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B_2)))),
% 0.45/0.70      inference('demod', [status(thm)], ['114', '115'])).
% 0.45/0.70  thf('123', plain, ((l1_pre_topc @ sk_B_2)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('124', plain, ((v2_pre_topc @ sk_B_2)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('125', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.45/0.70          | (m1_pre_topc @ sk_B_2 @ X0)
% 0.45/0.70          | ~ (l1_pre_topc @ X0))),
% 0.45/0.70      inference('demod', [status(thm)],
% 0.45/0.70                ['113', '116', '117', '118', '119', '120', '121', '122', 
% 0.45/0.70                 '123', '124'])).
% 0.45/0.70  thf('126', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['109', '125'])).
% 0.45/0.70  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('128', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.45/0.70      inference('demod', [status(thm)], ['126', '127'])).
% 0.45/0.70  thf('129', plain, ($false), inference('demod', [status(thm)], ['104', '128'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.54/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
