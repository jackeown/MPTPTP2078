%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H8g3BUwFCP

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:02 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 138 expanded)
%              Number of leaves         :   54 (  70 expanded)
%              Depth                    :   19
%              Number of atoms          :  660 (1630 expanded)
%              Number of equality atoms :    7 (  35 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X31: $i] :
      ( ~ ( v2_pre_topc @ X31 )
      | ( r2_hidden @ ( u1_struct_0 @ X31 ) @ ( u1_pre_topc @ X31 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X35 @ ( u1_pre_topc @ X36 ) )
      | ( v3_pre_topc @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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
    ! [X38: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X38 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X40: $i] :
      ( ~ ( v3_pre_topc @ X40 @ sk_A )
      | ~ ( v4_pre_topc @ X40 @ sk_A )
      | ~ ( r2_hidden @ sk_B_3 @ X40 )
      | ( r2_hidden @ X40 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X40: $i] :
      ( ~ ( v3_pre_topc @ X40 @ sk_A )
      | ~ ( v4_pre_topc @ X40 @ sk_A )
      | ~ ( r2_hidden @ sk_B_3 @ X40 )
      | ( r2_hidden @ X40 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
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
    ! [X37: $i] :
      ( ( l1_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
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
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
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
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_xboole_0 @ ( sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X39: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_2 @ X39 ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H8g3BUwFCP
% 0.15/0.36  % Computer   : n021.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:58:35 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.24/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.59  % Solved by: fo/fo7.sh
% 0.24/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.59  % done 191 iterations in 0.113s
% 0.24/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.59  % SZS output start Refutation
% 0.24/0.59  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.24/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.59  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.24/0.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.24/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.59  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.24/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.24/0.59  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.24/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.59  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.24/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.24/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.59  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.24/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.24/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.24/0.59  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.24/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.24/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.24/0.59  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.24/0.59  thf(t28_connsp_2, conjecture,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.59       ( ![B:$i]:
% 0.24/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.59           ( ![C:$i]:
% 0.24/0.59             ( ( m1_subset_1 @
% 0.24/0.59                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.59               ( ~( ( ![D:$i]:
% 0.24/0.59                      ( ( m1_subset_1 @
% 0.24/0.59                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.59                        ( ( r2_hidden @ D @ C ) <=>
% 0.24/0.59                          ( ( v3_pre_topc @ D @ A ) & 
% 0.24/0.59                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.24/0.59                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.24/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.59    (~( ![A:$i]:
% 0.24/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.59            ( l1_pre_topc @ A ) ) =>
% 0.24/0.59          ( ![B:$i]:
% 0.24/0.59            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.59              ( ![C:$i]:
% 0.24/0.59                ( ( m1_subset_1 @
% 0.24/0.59                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.59                  ( ~( ( ![D:$i]:
% 0.24/0.59                         ( ( m1_subset_1 @
% 0.24/0.59                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.59                           ( ( r2_hidden @ D @ C ) <=>
% 0.24/0.59                             ( ( v3_pre_topc @ D @ A ) & 
% 0.24/0.59                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.24/0.59                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.24/0.59    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.24/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('1', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf(t2_subset, axiom,
% 0.24/0.59    (![A:$i,B:$i]:
% 0.24/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.24/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.24/0.59  thf('2', plain,
% 0.24/0.59      (![X5 : $i, X6 : $i]:
% 0.24/0.59         ((r2_hidden @ X5 @ X6)
% 0.24/0.59          | (v1_xboole_0 @ X6)
% 0.24/0.59          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.24/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.24/0.59  thf('3', plain,
% 0.24/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.59  thf(d1_pre_topc, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( l1_pre_topc @ A ) =>
% 0.24/0.59       ( ( v2_pre_topc @ A ) <=>
% 0.24/0.59         ( ( ![B:$i]:
% 0.24/0.59             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.59               ( ![C:$i]:
% 0.24/0.59                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.59                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.24/0.59                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.24/0.59                     ( r2_hidden @
% 0.24/0.59                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.24/0.59                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.24/0.59           ( ![B:$i]:
% 0.24/0.59             ( ( m1_subset_1 @
% 0.24/0.59                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.59               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.24/0.59                 ( r2_hidden @
% 0.24/0.59                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.24/0.59                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.24/0.59           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.24/0.59  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.24/0.59  thf(zf_stmt_2, axiom,
% 0.24/0.59    (![B:$i,A:$i]:
% 0.24/0.59     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.24/0.59       ( ( m1_subset_1 @
% 0.24/0.59           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.59         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.24/0.59  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.24/0.59  thf(zf_stmt_4, axiom,
% 0.24/0.59    (![B:$i,A:$i]:
% 0.24/0.59     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.24/0.59       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.24/0.59         ( r2_hidden @
% 0.24/0.59           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.24/0.59  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.24/0.59  thf(zf_stmt_6, axiom,
% 0.24/0.59    (![B:$i,A:$i]:
% 0.24/0.59     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.24/0.59       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.59         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.24/0.59  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.24/0.59  thf(zf_stmt_8, axiom,
% 0.24/0.59    (![C:$i,B:$i,A:$i]:
% 0.24/0.59     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.24/0.59       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.59         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.24/0.59  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.24/0.59  thf(zf_stmt_10, axiom,
% 0.24/0.59    (![C:$i,B:$i,A:$i]:
% 0.24/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.24/0.59       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.24/0.59         ( r2_hidden @
% 0.24/0.59           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.24/0.59  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.24/0.59  thf(zf_stmt_12, axiom,
% 0.24/0.59    (![C:$i,B:$i,A:$i]:
% 0.24/0.59     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.24/0.59       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.24/0.59         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.24/0.59  thf(zf_stmt_13, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( l1_pre_topc @ A ) =>
% 0.24/0.59       ( ( v2_pre_topc @ A ) <=>
% 0.24/0.59         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.24/0.59           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.24/0.59           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.24/0.59  thf('4', plain,
% 0.24/0.59      (![X31 : $i]:
% 0.24/0.59         (~ (v2_pre_topc @ X31)
% 0.24/0.59          | (r2_hidden @ (u1_struct_0 @ X31) @ (u1_pre_topc @ X31))
% 0.24/0.59          | ~ (l1_pre_topc @ X31))),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.24/0.59  thf(dt_k2_subset_1, axiom,
% 0.24/0.59    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.59  thf('5', plain,
% 0.24/0.59      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.24/0.59      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.24/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.24/0.59  thf('6', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.24/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.24/0.59  thf('7', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.24/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.59  thf(d5_pre_topc, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( l1_pre_topc @ A ) =>
% 0.24/0.59       ( ![B:$i]:
% 0.24/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.59           ( ( v3_pre_topc @ B @ A ) <=>
% 0.24/0.59             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.24/0.59  thf('8', plain,
% 0.24/0.59      (![X35 : $i, X36 : $i]:
% 0.24/0.59         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.24/0.59          | ~ (r2_hidden @ X35 @ (u1_pre_topc @ X36))
% 0.24/0.59          | (v3_pre_topc @ X35 @ X36)
% 0.24/0.59          | ~ (l1_pre_topc @ X36))),
% 0.24/0.59      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.24/0.59  thf('9', plain,
% 0.24/0.59      (![X0 : $i]:
% 0.24/0.59         (~ (l1_pre_topc @ X0)
% 0.24/0.59          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.24/0.59          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.24/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.59  thf('10', plain,
% 0.24/0.59      (![X0 : $i]:
% 0.24/0.59         (~ (l1_pre_topc @ X0)
% 0.24/0.59          | ~ (v2_pre_topc @ X0)
% 0.24/0.59          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.24/0.59          | ~ (l1_pre_topc @ X0))),
% 0.24/0.59      inference('sup-', [status(thm)], ['4', '9'])).
% 0.24/0.59  thf('11', plain,
% 0.24/0.59      (![X0 : $i]:
% 0.24/0.59         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.24/0.59          | ~ (v2_pre_topc @ X0)
% 0.24/0.59          | ~ (l1_pre_topc @ X0))),
% 0.24/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.24/0.59  thf(fc4_pre_topc, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.59       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.24/0.59  thf('12', plain,
% 0.24/0.59      (![X38 : $i]:
% 0.24/0.59         ((v4_pre_topc @ (k2_struct_0 @ X38) @ X38)
% 0.24/0.59          | ~ (l1_pre_topc @ X38)
% 0.24/0.59          | ~ (v2_pre_topc @ X38))),
% 0.24/0.59      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.24/0.59  thf(d3_struct_0, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.24/0.59  thf('13', plain,
% 0.24/0.59      (![X34 : $i]:
% 0.24/0.59         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.24/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.59  thf('14', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.24/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.59  thf('15', plain,
% 0.24/0.59      (![X40 : $i]:
% 0.24/0.59         (~ (v3_pre_topc @ X40 @ sk_A)
% 0.24/0.59          | ~ (v4_pre_topc @ X40 @ sk_A)
% 0.24/0.59          | ~ (r2_hidden @ sk_B_3 @ X40)
% 0.24/0.59          | (r2_hidden @ X40 @ sk_C_1)
% 0.24/0.59          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('16', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('17', plain,
% 0.24/0.59      (![X40 : $i]:
% 0.24/0.59         (~ (v3_pre_topc @ X40 @ sk_A)
% 0.24/0.59          | ~ (v4_pre_topc @ X40 @ sk_A)
% 0.24/0.59          | ~ (r2_hidden @ sk_B_3 @ X40)
% 0.24/0.59          | (r2_hidden @ X40 @ k1_xboole_0)
% 0.24/0.59          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.59      inference('demod', [status(thm)], ['15', '16'])).
% 0.24/0.59  thf('18', plain,
% 0.24/0.59      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.24/0.59        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.24/0.59        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.24/0.59      inference('sup-', [status(thm)], ['14', '17'])).
% 0.24/0.59  thf('19', plain,
% 0.24/0.59      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.24/0.59        | ~ (l1_struct_0 @ sk_A)
% 0.24/0.59        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.24/0.59        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.24/0.59      inference('sup-', [status(thm)], ['13', '18'])).
% 0.24/0.59  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf(dt_l1_pre_topc, axiom,
% 0.24/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.59  thf('21', plain,
% 0.24/0.59      (![X37 : $i]: ((l1_struct_0 @ X37) | ~ (l1_pre_topc @ X37))),
% 0.24/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.59  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.59  thf('23', plain,
% 0.24/0.59      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.24/0.59        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.24/0.59        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.24/0.59      inference('demod', [status(thm)], ['19', '22'])).
% 0.24/0.59  thf('24', plain,
% 0.24/0.59      ((~ (v2_pre_topc @ sk_A)
% 0.24/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.59        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.24/0.59        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.24/0.59      inference('sup-', [status(thm)], ['12', '23'])).
% 0.24/0.59  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('27', plain,
% 0.24/0.59      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.24/0.59        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.24/0.59      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.24/0.59  thf('28', plain,
% 0.24/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.59        | ~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.24/0.59      inference('sup-', [status(thm)], ['11', '27'])).
% 0.24/0.59  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('31', plain,
% 0.24/0.59      ((~ (r2_hidden @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.24/0.59      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.24/0.59  thf('32', plain,
% 0.24/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.24/0.59      inference('sup-', [status(thm)], ['3', '31'])).
% 0.24/0.59  thf(t7_ordinal1, axiom,
% 0.24/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.59  thf('33', plain,
% 0.24/0.59      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.24/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.24/0.59  thf('34', plain,
% 0.24/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.59        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.24/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.59  thf('35', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.59  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.24/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.59  thf(rc7_pre_topc, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.59       ( ?[B:$i]:
% 0.24/0.59         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.24/0.59           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.24/0.59  thf('37', plain,
% 0.24/0.59      (![X39 : $i]:
% 0.24/0.59         ((m1_subset_1 @ (sk_B_2 @ X39) @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.24/0.59          | ~ (l1_pre_topc @ X39)
% 0.24/0.59          | ~ (v2_pre_topc @ X39)
% 0.24/0.59          | (v2_struct_0 @ X39))),
% 0.24/0.59      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.24/0.59  thf(cc1_subset_1, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.24/0.59       ( ![B:$i]:
% 0.24/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.24/0.59  thf('38', plain,
% 0.24/0.59      (![X3 : $i, X4 : $i]:
% 0.24/0.59         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.24/0.59          | (v1_xboole_0 @ X3)
% 0.24/0.59          | ~ (v1_xboole_0 @ X4))),
% 0.24/0.59      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.24/0.59  thf('39', plain,
% 0.24/0.59      (![X0 : $i]:
% 0.24/0.59         ((v2_struct_0 @ X0)
% 0.24/0.59          | ~ (v2_pre_topc @ X0)
% 0.24/0.59          | ~ (l1_pre_topc @ X0)
% 0.24/0.59          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.24/0.59          | (v1_xboole_0 @ (sk_B_2 @ X0)))),
% 0.24/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.24/0.59  thf('40', plain,
% 0.24/0.59      (((v1_xboole_0 @ (sk_B_2 @ sk_A))
% 0.24/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.59        | (v2_struct_0 @ sk_A))),
% 0.24/0.59      inference('sup-', [status(thm)], ['36', '39'])).
% 0.24/0.59  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('43', plain, (((v1_xboole_0 @ (sk_B_2 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.24/0.59      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.24/0.59  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('45', plain, ((v1_xboole_0 @ (sk_B_2 @ sk_A))),
% 0.24/0.59      inference('clc', [status(thm)], ['43', '44'])).
% 0.24/0.59  thf('46', plain,
% 0.24/0.59      (![X39 : $i]:
% 0.24/0.59         (~ (v1_xboole_0 @ (sk_B_2 @ X39))
% 0.24/0.59          | ~ (l1_pre_topc @ X39)
% 0.24/0.59          | ~ (v2_pre_topc @ X39)
% 0.24/0.59          | (v2_struct_0 @ X39))),
% 0.24/0.59      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.24/0.59  thf('47', plain,
% 0.24/0.59      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.24/0.59  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.24/0.59      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.24/0.59  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.24/0.59  
% 0.24/0.59  % SZS output end Refutation
% 0.24/0.59  
% 0.24/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
