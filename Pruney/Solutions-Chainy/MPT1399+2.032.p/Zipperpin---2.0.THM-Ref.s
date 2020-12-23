%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JlX0avlxo9

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 125 expanded)
%              Number of leaves         :   53 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  578 (1326 expanded)
%              Number of equality atoms :   15 (  37 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
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
    ! [X39: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X39 ) @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
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
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X40: $i] :
      ( ~ ( v3_pre_topc @ X40 @ sk_A )
      | ~ ( v4_pre_topc @ X40 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X40 )
      | ( r2_hidden @ X40 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X37: $i] :
      ( ( l1_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('42',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JlX0avlxo9
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:14:18 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 118 iterations in 0.079s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.19/0.53  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.19/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.19/0.53  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.19/0.53  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.19/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.19/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.19/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.19/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.53  thf(t28_connsp_2, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( m1_subset_1 @
% 0.19/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.53               ( ~( ( ![D:$i]:
% 0.19/0.53                      ( ( m1_subset_1 @
% 0.19/0.53                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53                        ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.53                          ( ( v3_pre_topc @ D @ A ) & 
% 0.19/0.53                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.19/0.53                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.53            ( l1_pre_topc @ A ) ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53              ( ![C:$i]:
% 0.19/0.53                ( ( m1_subset_1 @
% 0.19/0.53                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.53                  ( ~( ( ![D:$i]:
% 0.19/0.53                         ( ( m1_subset_1 @
% 0.19/0.53                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53                           ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.53                             ( ( v3_pre_topc @ D @ A ) & 
% 0.19/0.53                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.19/0.53                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.19/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t2_subset, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X7 : $i, X8 : $i]:
% 0.19/0.53         ((r2_hidden @ X7 @ X8)
% 0.19/0.53          | (v1_xboole_0 @ X8)
% 0.19/0.53          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.19/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf(d1_pre_topc, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ( v2_pre_topc @ A ) <=>
% 0.19/0.53         ( ( ![B:$i]:
% 0.19/0.53             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53               ( ![C:$i]:
% 0.19/0.53                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.19/0.53                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.19/0.53                     ( r2_hidden @
% 0.19/0.53                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.19/0.53                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.19/0.53           ( ![B:$i]:
% 0.19/0.53             ( ( m1_subset_1 @
% 0.19/0.53                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.53               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.19/0.53                 ( r2_hidden @
% 0.19/0.53                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.19/0.53                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.19/0.53           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_2, axiom,
% 0.19/0.53    (![B:$i,A:$i]:
% 0.19/0.53     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.19/0.53       ( ( m1_subset_1 @
% 0.19/0.53           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.53         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.19/0.53  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_4, axiom,
% 0.19/0.53    (![B:$i,A:$i]:
% 0.19/0.53     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.19/0.53       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.19/0.53         ( r2_hidden @
% 0.19/0.53           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_6, axiom,
% 0.19/0.53    (![B:$i,A:$i]:
% 0.19/0.53     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.19/0.53       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_8, axiom,
% 0.19/0.53    (![C:$i,B:$i,A:$i]:
% 0.19/0.53     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.19/0.53       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.19/0.53  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_10, axiom,
% 0.19/0.53    (![C:$i,B:$i,A:$i]:
% 0.19/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.19/0.53       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.19/0.53         ( r2_hidden @
% 0.19/0.53           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_12, axiom,
% 0.19/0.53    (![C:$i,B:$i,A:$i]:
% 0.19/0.53     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.19/0.53       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.19/0.53         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_13, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ( v2_pre_topc @ A ) <=>
% 0.19/0.53         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.19/0.53           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.19/0.53           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X31 : $i]:
% 0.19/0.53         (~ (v2_pre_topc @ X31)
% 0.19/0.53          | (r2_hidden @ (u1_struct_0 @ X31) @ (u1_pre_topc @ X31))
% 0.19/0.53          | ~ (l1_pre_topc @ X31))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.19/0.53  thf(dt_k2_subset_1, axiom,
% 0.19/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.53  thf('6', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.53  thf('7', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.19/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf(d5_pre_topc, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v3_pre_topc @ B @ A ) <=>
% 0.19/0.53             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X35 : $i, X36 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.19/0.53          | ~ (r2_hidden @ X35 @ (u1_pre_topc @ X36))
% 0.19/0.53          | (v3_pre_topc @ X35 @ X36)
% 0.19/0.53          | ~ (l1_pre_topc @ X36))),
% 0.19/0.53      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (l1_pre_topc @ X0)
% 0.19/0.53          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.19/0.53          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (l1_pre_topc @ X0)
% 0.19/0.53          | ~ (v2_pre_topc @ X0)
% 0.19/0.53          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.19/0.53          | ~ (l1_pre_topc @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.19/0.53          | ~ (v2_pre_topc @ X0)
% 0.19/0.53          | ~ (l1_pre_topc @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.53  thf(fc4_pre_topc, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X39 : $i]:
% 0.19/0.53         ((v4_pre_topc @ (k2_struct_0 @ X39) @ X39)
% 0.19/0.53          | ~ (l1_pre_topc @ X39)
% 0.19/0.53          | ~ (v2_pre_topc @ X39))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.19/0.53  thf(d3_struct_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X34 : $i]:
% 0.19/0.53         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.53  thf('14', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.19/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X40 : $i]:
% 0.19/0.53         (~ (v3_pre_topc @ X40 @ sk_A)
% 0.19/0.53          | ~ (v4_pre_topc @ X40 @ sk_A)
% 0.19/0.53          | ~ (r2_hidden @ sk_B_2 @ X40)
% 0.19/0.53          | (r2_hidden @ X40 @ sk_C_1)
% 0.19/0.53          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.19/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(dt_l1_pre_topc, axiom,
% 0.19/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X37 : $i]: ((l1_struct_0 @ X37) | ~ (l1_pre_topc @ X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.53  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['17', '20'])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['12', '21'])).
% 0.19/0.53  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.53  thf(t113_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i]:
% 0.19/0.53         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.53  thf('28', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('29', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('30', plain, (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ sk_C_1) = (sk_C_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.19/0.53  thf(t152_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.19/0.53      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.19/0.53  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.19/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('clc', [status(thm)], ['25', '32'])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['11', '33'])).
% 0.19/0.53  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('37', plain, (~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.19/0.53  thf('38', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '37'])).
% 0.19/0.53  thf(fc2_struct_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (![X38 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X38))
% 0.19/0.53          | ~ (l1_struct_0 @ X38)
% 0.19/0.53          | (v2_struct_0 @ X38))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.53  thf('40', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.53  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('42', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.53  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
