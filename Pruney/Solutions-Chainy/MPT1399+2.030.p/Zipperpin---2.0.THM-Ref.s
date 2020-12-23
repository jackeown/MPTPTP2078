%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uenylQkkYr

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:06 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 145 expanded)
%              Number of leaves         :   58 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  710 (1683 expanded)
%              Number of equality atoms :   10 (  38 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X38: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ( r2_hidden @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( r2_hidden @ X42 @ ( u1_pre_topc @ X43 ) )
      | ( v3_pre_topc @ X42 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('13',plain,(
    ! [X45: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X45 ) @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('16',plain,(
    ! [X47: $i] :
      ( ~ ( v3_pre_topc @ X47 @ sk_A )
      | ~ ( v4_pre_topc @ X47 @ sk_A )
      | ~ ( r2_hidden @ sk_B_4 @ X47 )
      | ( r2_hidden @ X47 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X47: $i] :
      ( ~ ( v3_pre_topc @ X47 @ sk_A )
      | ~ ( v4_pre_topc @ X47 @ sk_A )
      | ~ ( r2_hidden @ sk_B_4 @ X47 )
      | ( r2_hidden @ X47 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('22',plain,(
    ! [X44: $i] :
      ( ( l1_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','32'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X46: $i] :
      ( ( m1_subset_1 @ ( sk_B_3 @ X46 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_3 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_3 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_3 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X46: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_3 @ X46 ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uenylQkkYr
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.72  % Solved by: fo/fo7.sh
% 0.45/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.72  % done 405 iterations in 0.254s
% 0.45/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.72  % SZS output start Refutation
% 0.45/0.72  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.72  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.72  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.72  thf(sk_B_3_type, type, sk_B_3: $i > $i).
% 0.45/0.72  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.45/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.72  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.72  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.45/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.72  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.45/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.72  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.72  thf(sk_B_4_type, type, sk_B_4: $i).
% 0.45/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.72  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.72  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.45/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.45/0.72  thf(t28_connsp_2, conjecture,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.72       ( ![B:$i]:
% 0.45/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.72           ( ![C:$i]:
% 0.45/0.72             ( ( m1_subset_1 @
% 0.45/0.72                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.72               ( ~( ( ![D:$i]:
% 0.45/0.72                      ( ( m1_subset_1 @
% 0.45/0.72                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.72                        ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.72                          ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.72                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.72                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.72    (~( ![A:$i]:
% 0.45/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.72            ( l1_pre_topc @ A ) ) =>
% 0.45/0.72          ( ![B:$i]:
% 0.45/0.72            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.72              ( ![C:$i]:
% 0.45/0.72                ( ( m1_subset_1 @
% 0.45/0.72                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.72                  ( ~( ( ![D:$i]:
% 0.45/0.72                         ( ( m1_subset_1 @
% 0.45/0.72                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.72                           ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.72                             ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.72                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.72                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.45/0.72    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.45/0.72  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf(t6_mcart_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.72          ( ![B:$i]:
% 0.45/0.72            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.72                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.72                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.45/0.72                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.45/0.72                       ( r2_hidden @ G @ B ) ) =>
% 0.45/0.72                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.72  thf('1', plain,
% 0.45/0.72      (![X10 : $i]:
% 0.45/0.72         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.45/0.72      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.45/0.72  thf('2', plain, ((m1_subset_1 @ sk_B_4 @ (u1_struct_0 @ sk_A))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf(t2_subset, axiom,
% 0.45/0.72    (![A:$i,B:$i]:
% 0.45/0.72     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.72       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.72  thf('3', plain,
% 0.45/0.72      (![X3 : $i, X4 : $i]:
% 0.45/0.72         ((r2_hidden @ X3 @ X4)
% 0.45/0.72          | (v1_xboole_0 @ X4)
% 0.45/0.72          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.45/0.72      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.72  thf('4', plain,
% 0.45/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.72  thf(d1_pre_topc, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( l1_pre_topc @ A ) =>
% 0.45/0.72       ( ( v2_pre_topc @ A ) <=>
% 0.45/0.72         ( ( ![B:$i]:
% 0.45/0.72             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.72               ( ![C:$i]:
% 0.45/0.72                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.72                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.72                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.45/0.72                     ( r2_hidden @
% 0.45/0.72                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.45/0.72                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.45/0.72           ( ![B:$i]:
% 0.45/0.72             ( ( m1_subset_1 @
% 0.45/0.72                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.72               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.45/0.72                 ( r2_hidden @
% 0.45/0.72                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.45/0.72                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.45/0.72           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.45/0.72  thf(zf_stmt_2, axiom,
% 0.45/0.72    (![B:$i,A:$i]:
% 0.45/0.72     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.45/0.72       ( ( m1_subset_1 @
% 0.45/0.72           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.72         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.45/0.72  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.45/0.72  thf(zf_stmt_4, axiom,
% 0.45/0.72    (![B:$i,A:$i]:
% 0.45/0.72     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.45/0.72       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.45/0.72         ( r2_hidden @
% 0.45/0.72           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.45/0.72  thf(zf_stmt_6, axiom,
% 0.45/0.72    (![B:$i,A:$i]:
% 0.45/0.72     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.45/0.72       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.72         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.72  thf(zf_stmt_8, axiom,
% 0.45/0.72    (![C:$i,B:$i,A:$i]:
% 0.45/0.72     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.45/0.72       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.72         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.45/0.72  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.72  thf(zf_stmt_10, axiom,
% 0.45/0.72    (![C:$i,B:$i,A:$i]:
% 0.45/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.45/0.72       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.45/0.72         ( r2_hidden @
% 0.45/0.72           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.45/0.72  thf(zf_stmt_12, axiom,
% 0.45/0.72    (![C:$i,B:$i,A:$i]:
% 0.45/0.72     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.45/0.72       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.72         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.72  thf(zf_stmt_13, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( l1_pre_topc @ A ) =>
% 0.45/0.72       ( ( v2_pre_topc @ A ) <=>
% 0.45/0.72         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.72           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.45/0.72           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.45/0.72  thf('5', plain,
% 0.45/0.72      (![X38 : $i]:
% 0.45/0.72         (~ (v2_pre_topc @ X38)
% 0.45/0.72          | (r2_hidden @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))
% 0.45/0.72          | ~ (l1_pre_topc @ X38))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.45/0.72  thf(dt_k2_subset_1, axiom,
% 0.45/0.72    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.72  thf('6', plain,
% 0.45/0.72      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.45/0.72  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.72  thf('7', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.45/0.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.72  thf('8', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.45/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.72  thf(d5_pre_topc, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( l1_pre_topc @ A ) =>
% 0.45/0.72       ( ![B:$i]:
% 0.45/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.72           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.72             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.45/0.72  thf('9', plain,
% 0.45/0.72      (![X42 : $i, X43 : $i]:
% 0.45/0.72         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.45/0.72          | ~ (r2_hidden @ X42 @ (u1_pre_topc @ X43))
% 0.45/0.72          | (v3_pre_topc @ X42 @ X43)
% 0.45/0.72          | ~ (l1_pre_topc @ X43))),
% 0.45/0.72      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.72  thf('10', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (l1_pre_topc @ X0)
% 0.45/0.72          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.72          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.72  thf('11', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (l1_pre_topc @ X0)
% 0.45/0.72          | ~ (v2_pre_topc @ X0)
% 0.45/0.72          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.72          | ~ (l1_pre_topc @ X0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['5', '10'])).
% 0.45/0.72  thf('12', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.72          | ~ (v2_pre_topc @ X0)
% 0.45/0.72          | ~ (l1_pre_topc @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.72  thf(fc4_pre_topc, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.72       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.72  thf('13', plain,
% 0.45/0.72      (![X45 : $i]:
% 0.45/0.72         ((v4_pre_topc @ (k2_struct_0 @ X45) @ X45)
% 0.45/0.72          | ~ (l1_pre_topc @ X45)
% 0.45/0.72          | ~ (v2_pre_topc @ X45))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.45/0.72  thf(d3_struct_0, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.72  thf('14', plain,
% 0.45/0.72      (![X41 : $i]:
% 0.45/0.72         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.45/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.72  thf('15', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.45/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.72  thf('16', plain,
% 0.45/0.72      (![X47 : $i]:
% 0.45/0.72         (~ (v3_pre_topc @ X47 @ sk_A)
% 0.45/0.72          | ~ (v4_pre_topc @ X47 @ sk_A)
% 0.45/0.72          | ~ (r2_hidden @ sk_B_4 @ X47)
% 0.45/0.72          | (r2_hidden @ X47 @ sk_C_1)
% 0.45/0.72          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('17', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('18', plain,
% 0.45/0.72      (![X47 : $i]:
% 0.45/0.72         (~ (v3_pre_topc @ X47 @ sk_A)
% 0.45/0.72          | ~ (v4_pre_topc @ X47 @ sk_A)
% 0.45/0.72          | ~ (r2_hidden @ sk_B_4 @ X47)
% 0.45/0.72          | (r2_hidden @ X47 @ k1_xboole_0)
% 0.45/0.72          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.72      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.72  thf('19', plain,
% 0.45/0.72      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.72        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.72        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['15', '18'])).
% 0.45/0.72  thf('20', plain,
% 0.45/0.72      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.72        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.72        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.72        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['14', '19'])).
% 0.45/0.72  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf(dt_l1_pre_topc, axiom,
% 0.45/0.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.72  thf('22', plain,
% 0.45/0.72      (![X44 : $i]: ((l1_struct_0 @ X44) | ~ (l1_pre_topc @ X44))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.72  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.72  thf('24', plain,
% 0.45/0.72      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.72        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.72        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.72      inference('demod', [status(thm)], ['20', '23'])).
% 0.45/0.72  thf('25', plain,
% 0.45/0.72      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.72        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.72        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['13', '24'])).
% 0.45/0.72  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('28', plain,
% 0.45/0.72      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.72        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.45/0.72  thf('29', plain,
% 0.45/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.72        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['12', '28'])).
% 0.45/0.72  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('32', plain,
% 0.45/0.72      ((~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.72      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.45/0.72  thf('33', plain,
% 0.45/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['4', '32'])).
% 0.45/0.72  thf(t7_ordinal1, axiom,
% 0.45/0.72    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.72  thf('34', plain,
% 0.45/0.72      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.45/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.72  thf('35', plain,
% 0.45/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.72        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.72  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.72  thf('37', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.72  thf(rc3_tops_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.72       ( ?[B:$i]:
% 0.45/0.72         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.45/0.72           ( ~( v1_xboole_0 @ B ) ) & 
% 0.45/0.72           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.72  thf('38', plain,
% 0.45/0.72      (![X46 : $i]:
% 0.45/0.72         ((m1_subset_1 @ (sk_B_3 @ X46) @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.45/0.72          | ~ (l1_pre_topc @ X46)
% 0.45/0.72          | ~ (v2_pre_topc @ X46)
% 0.45/0.72          | (v2_struct_0 @ X46))),
% 0.45/0.72      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.45/0.72  thf(t5_subset, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.72          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.72  thf('39', plain,
% 0.45/0.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.72         (~ (r2_hidden @ X5 @ X6)
% 0.45/0.72          | ~ (v1_xboole_0 @ X7)
% 0.45/0.72          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.45/0.72      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.72  thf('40', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         ((v2_struct_0 @ X0)
% 0.45/0.72          | ~ (v2_pre_topc @ X0)
% 0.45/0.72          | ~ (l1_pre_topc @ X0)
% 0.45/0.72          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.72          | ~ (r2_hidden @ X1 @ (sk_B_3 @ X0)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.72  thf('41', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (r2_hidden @ X0 @ (sk_B_3 @ sk_A))
% 0.45/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.72          | (v2_struct_0 @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['37', '40'])).
% 0.45/0.72  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('44', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (r2_hidden @ X0 @ (sk_B_3 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.45/0.72  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_3 @ sk_A))),
% 0.45/0.72      inference('clc', [status(thm)], ['44', '45'])).
% 0.45/0.72  thf('47', plain, (((sk_B_3 @ sk_A) = (k1_xboole_0))),
% 0.45/0.72      inference('sup-', [status(thm)], ['1', '46'])).
% 0.45/0.72  thf('48', plain,
% 0.45/0.72      (![X46 : $i]:
% 0.45/0.72         (~ (v1_xboole_0 @ (sk_B_3 @ X46))
% 0.45/0.72          | ~ (l1_pre_topc @ X46)
% 0.45/0.72          | ~ (v2_pre_topc @ X46)
% 0.45/0.72          | (v2_struct_0 @ X46))),
% 0.45/0.72      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.45/0.72  thf('49', plain,
% 0.45/0.72      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.72        | (v2_struct_0 @ sk_A)
% 0.45/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.72  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.72  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('53', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.72      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.45/0.72  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 0.45/0.72  
% 0.45/0.72  % SZS output end Refutation
% 0.45/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
