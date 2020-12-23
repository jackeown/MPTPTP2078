%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LmkWAizWrk

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:06 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 224 expanded)
%              Number of leaves         :   60 (  98 expanded)
%              Depth                    :   20
%              Number of atoms          :  738 (2664 expanded)
%              Number of equality atoms :   17 (  69 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X39: $i] :
      ( ( ( k2_struct_0 @ X39 )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X36: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ( r2_hidden @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( r2_hidden @ X40 @ ( u1_pre_topc @ X41 ) )
      | ( v3_pre_topc @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('12',plain,(
    ! [X43: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('13',plain,(
    ! [X39: $i] :
      ( ( ( k2_struct_0 @ X39 )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X46: $i] :
      ( ~ ( v3_pre_topc @ X46 @ sk_A )
      | ~ ( v4_pre_topc @ X46 @ sk_A )
      | ~ ( r2_hidden @ sk_B_4 @ X46 )
      | ( r2_hidden @ X46 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X46: $i] :
      ( ~ ( v3_pre_topc @ X46 @ sk_A )
      | ~ ( v4_pre_topc @ X46 @ sk_A )
      | ~ ( r2_hidden @ sk_B_4 @ X46 )
      | ( r2_hidden @ X46 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X42: $i] :
      ( ( l1_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','31'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('41',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf(fc14_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ~ ( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('42',plain,(
    ! [X45: $i] :
      ( ~ ( v2_tops_1 @ ( k2_struct_0 @ X45 ) @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc14_tops_1])).

thf('43',plain,
    ( ~ ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( v2_tops_1 @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('49',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('50',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(rc5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v2_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ ( sk_B_3 @ X44 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[rc5_tops_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_3 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B_3 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X44: $i] :
      ( ( v2_tops_1 @ ( sk_B_3 @ X44 ) @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[rc5_tops_1])).

thf('59',plain,
    ( ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_tops_1 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['48','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LmkWAizWrk
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 311 iterations in 0.208s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.46/0.63  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.46/0.63  thf(sk_B_3_type, type, sk_B_3: $i > $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.63  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.46/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.46/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.63  thf(sk_B_4_type, type, sk_B_4: $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.63  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.46/0.63  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.46/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.46/0.63  thf(d3_struct_0, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (![X39 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X39) = (u1_struct_0 @ X39)) | ~ (l1_struct_0 @ X39))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf(t28_connsp_2, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @
% 0.46/0.63                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63               ( ~( ( ![D:$i]:
% 0.46/0.63                      ( ( m1_subset_1 @
% 0.46/0.63                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                        ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.63                          ( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.63                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.46/0.63                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.63            ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63              ( ![C:$i]:
% 0.46/0.63                ( ( m1_subset_1 @
% 0.46/0.63                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63                  ( ~( ( ![D:$i]:
% 0.46/0.63                         ( ( m1_subset_1 @
% 0.46/0.63                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                           ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.63                             ( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.63                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.46/0.63                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.46/0.63  thf('1', plain, ((m1_subset_1 @ sk_B_4 @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t2_subset, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X4 : $i, X5 : $i]:
% 0.46/0.63         ((r2_hidden @ X4 @ X5)
% 0.46/0.63          | (v1_xboole_0 @ X5)
% 0.46/0.63          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf(d1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ( v2_pre_topc @ A ) <=>
% 0.46/0.63         ( ( ![B:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ![C:$i]:
% 0.46/0.63                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.63                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.46/0.63                     ( r2_hidden @
% 0.46/0.63                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.46/0.63                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.46/0.63           ( ![B:$i]:
% 0.46/0.63             ( ( m1_subset_1 @
% 0.46/0.63                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.46/0.63                 ( r2_hidden @
% 0.46/0.63                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.46/0.63                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.46/0.63           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_2, axiom,
% 0.46/0.63    (![B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.46/0.63       ( ( m1_subset_1 @
% 0.46/0.63           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.46/0.63  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_4, axiom,
% 0.46/0.63    (![B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.46/0.63       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.46/0.63         ( r2_hidden @
% 0.46/0.63           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_6, axiom,
% 0.46/0.63    (![B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.46/0.63       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_8, axiom,
% 0.46/0.63    (![C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.46/0.63       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.46/0.63  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_10, axiom,
% 0.46/0.63    (![C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.46/0.63       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.46/0.63         ( r2_hidden @
% 0.46/0.63           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_12, axiom,
% 0.46/0.63    (![C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.46/0.63       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.63         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_13, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ( v2_pre_topc @ A ) <=>
% 0.46/0.63         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.63           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.46/0.63           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X36 : $i]:
% 0.46/0.63         (~ (v2_pre_topc @ X36)
% 0.46/0.63          | (r2_hidden @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36))
% 0.46/0.63          | ~ (l1_pre_topc @ X36))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.46/0.63  thf(dt_k2_subset_1, axiom,
% 0.46/0.63    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.46/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.63  thf('6', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.63  thf('7', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.46/0.63      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.63  thf(d5_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.63             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X40 : $i, X41 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.46/0.63          | ~ (r2_hidden @ X40 @ (u1_pre_topc @ X41))
% 0.46/0.63          | (v3_pre_topc @ X40 @ X41)
% 0.46/0.63          | ~ (l1_pre_topc @ X41))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.63          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | ~ (v2_pre_topc @ X0)
% 0.46/0.63          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.63          | ~ (l1_pre_topc @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '9'])).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.63          | ~ (v2_pre_topc @ X0)
% 0.46/0.63          | ~ (l1_pre_topc @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.63  thf(fc4_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X43 : $i]:
% 0.46/0.63         ((v4_pre_topc @ (k2_struct_0 @ X43) @ X43)
% 0.46/0.63          | ~ (l1_pre_topc @ X43)
% 0.46/0.63          | ~ (v2_pre_topc @ X43))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X39 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X39) = (u1_struct_0 @ X39)) | ~ (l1_struct_0 @ X39))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('14', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.46/0.63      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X46 : $i]:
% 0.46/0.63         (~ (v3_pre_topc @ X46 @ sk_A)
% 0.46/0.63          | ~ (v4_pre_topc @ X46 @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ sk_B_4 @ X46)
% 0.46/0.63          | (r2_hidden @ X46 @ sk_C_1)
% 0.46/0.63          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('16', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X46 : $i]:
% 0.46/0.63         (~ (v3_pre_topc @ X46 @ sk_A)
% 0.46/0.63          | ~ (v4_pre_topc @ X46 @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ sk_B_4 @ X46)
% 0.46/0.63          | (r2_hidden @ X46 @ k1_xboole_0)
% 0.46/0.63          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.46/0.63        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['14', '17'])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.46/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.63        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['13', '18'])).
% 0.46/0.63  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_l1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X42 : $i]: ((l1_struct_0 @ X42) | ~ (l1_pre_topc @ X42))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.63  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.46/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.63        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['19', '22'])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      ((~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.46/0.63        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['12', '23'])).
% 0.46/0.63  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.46/0.63        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['11', '27'])).
% 0.46/0.63  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      ((~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '31'])).
% 0.46/0.63  thf(t7_ordinal1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.63  thf('35', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.46/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.63  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf(l13_xboole_0, axiom,
% 0.46/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.63  thf('38', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['0', '38'])).
% 0.46/0.63  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('41', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.63  thf(fc14_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ~( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X45 : $i]:
% 0.46/0.63         (~ (v2_tops_1 @ (k2_struct_0 @ X45) @ X45)
% 0.46/0.63          | ~ (l1_pre_topc @ X45)
% 0.46/0.63          | ~ (v2_pre_topc @ X45)
% 0.46/0.63          | (v2_struct_0 @ X45))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc14_tops_1])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      ((~ (v2_tops_1 @ k1_xboole_0 @ sk_A)
% 0.46/0.63        | (v2_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.63  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      ((~ (v2_tops_1 @ k1_xboole_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.46/0.63  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('48', plain, (~ (v2_tops_1 @ k1_xboole_0 @ sk_A)),
% 0.46/0.63      inference('clc', [status(thm)], ['46', '47'])).
% 0.46/0.63  thf(t9_mcart_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ~( ( r2_hidden @ B @ A ) & 
% 0.46/0.63                 ( ![C:$i,D:$i]:
% 0.46/0.63                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.46/0.63                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      (![X11 : $i]:
% 0.46/0.63         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.46/0.63  thf('50', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf(rc5_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ?[B:$i]:
% 0.46/0.63         ( ( v2_tops_1 @ B @ A ) & 
% 0.46/0.63           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X44 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (sk_B_3 @ X44) @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.46/0.63          | ~ (l1_pre_topc @ X44))),
% 0.46/0.63      inference('cnf', [status(esa)], [rc5_tops_1])).
% 0.46/0.63  thf(t5_subset, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.63          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X6 @ X7)
% 0.46/0.63          | ~ (v1_xboole_0 @ X8)
% 0.46/0.63          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.46/0.63          | ~ (r2_hidden @ X1 @ (sk_B_3 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ (sk_B_3 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['50', '53'])).
% 0.46/0.63  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_3 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.63  thf('57', plain, (((sk_B_3 @ sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['49', '56'])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      (![X44 : $i]:
% 0.46/0.63         ((v2_tops_1 @ (sk_B_3 @ X44) @ X44) | ~ (l1_pre_topc @ X44))),
% 0.46/0.63      inference('cnf', [status(esa)], [rc5_tops_1])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      (((v2_tops_1 @ k1_xboole_0 @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.63  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('61', plain, ((v2_tops_1 @ k1_xboole_0 @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.63  thf('62', plain, ($false), inference('demod', [status(thm)], ['48', '61'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
