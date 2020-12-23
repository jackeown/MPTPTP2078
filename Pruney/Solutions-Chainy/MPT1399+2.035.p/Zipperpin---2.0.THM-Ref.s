%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KvgiCzmsZc

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:07 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 134 expanded)
%              Number of leaves         :   56 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  701 (1317 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X36: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ( r2_hidden @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r2_hidden @ X39 @ ( u1_pre_topc @ X40 ) )
      | ( v3_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('12',plain,(
    ! [X43: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X43 ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r2_hidden @ X39 @ ( u1_pre_topc @ X40 ) )
      | ( v3_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ X44 @ X45 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('30',plain,(
    ! [X46: $i] :
      ( ~ ( v3_pre_topc @ X46 @ sk_A )
      | ~ ( v4_pre_topc @ X46 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X46 )
      | ( r2_hidden @ X46 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X46: $i] :
      ( ~ ( v3_pre_topc @ X46 @ sk_A )
      | ~ ( v4_pre_topc @ X46 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X46 )
      | ( r2_hidden @ X46 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','41'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X42: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X41: $i] :
      ( ( l1_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KvgiCzmsZc
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 175 iterations in 0.086s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.36/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.56  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.36/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.36/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.36/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.36/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.56  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.36/0.56  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.36/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.56  thf(t28_connsp_2, conjecture,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @
% 0.36/0.56                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.56               ( ~( ( ![D:$i]:
% 0.36/0.56                      ( ( m1_subset_1 @
% 0.36/0.56                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                        ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.56                          ( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.56                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.36/0.56                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i]:
% 0.36/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.56            ( l1_pre_topc @ A ) ) =>
% 0.36/0.56          ( ![B:$i]:
% 0.36/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56              ( ![C:$i]:
% 0.36/0.56                ( ( m1_subset_1 @
% 0.36/0.56                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.56                  ( ~( ( ![D:$i]:
% 0.36/0.56                         ( ( m1_subset_1 @
% 0.36/0.56                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                           ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.56                             ( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.56                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.36/0.56                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.36/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t2_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         ((r2_hidden @ X7 @ X8)
% 0.36/0.56          | (v1_xboole_0 @ X8)
% 0.36/0.56          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.56  thf(d1_pre_topc, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ( v2_pre_topc @ A ) <=>
% 0.36/0.56         ( ( ![B:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ![C:$i]:
% 0.36/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.36/0.56                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.36/0.56                     ( r2_hidden @
% 0.36/0.56                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.36/0.56                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.36/0.56           ( ![B:$i]:
% 0.36/0.56             ( ( m1_subset_1 @
% 0.36/0.56                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.56               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.36/0.56                 ( r2_hidden @
% 0.36/0.56                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.36/0.56                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.36/0.56           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.36/0.56  thf(zf_stmt_2, axiom,
% 0.36/0.56    (![B:$i,A:$i]:
% 0.36/0.56     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.36/0.56       ( ( m1_subset_1 @
% 0.36/0.56           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.56         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.36/0.56  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.36/0.56  thf(zf_stmt_4, axiom,
% 0.36/0.56    (![B:$i,A:$i]:
% 0.36/0.56     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.36/0.56       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.36/0.56         ( r2_hidden @
% 0.36/0.56           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.36/0.56  thf(zf_stmt_6, axiom,
% 0.36/0.56    (![B:$i,A:$i]:
% 0.36/0.56     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.36/0.56       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.36/0.56  thf(zf_stmt_8, axiom,
% 0.36/0.56    (![C:$i,B:$i,A:$i]:
% 0.36/0.56     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.36/0.56       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.36/0.56  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.56  thf(zf_stmt_10, axiom,
% 0.36/0.56    (![C:$i,B:$i,A:$i]:
% 0.36/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.36/0.56       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.36/0.56         ( r2_hidden @
% 0.36/0.56           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.36/0.56  thf(zf_stmt_12, axiom,
% 0.36/0.56    (![C:$i,B:$i,A:$i]:
% 0.36/0.56     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.36/0.56       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.36/0.56         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_13, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ( v2_pre_topc @ A ) <=>
% 0.36/0.56         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.36/0.56           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.36/0.56           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X36 : $i]:
% 0.36/0.56         (~ (v2_pre_topc @ X36)
% 0.36/0.56          | (r2_hidden @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36))
% 0.36/0.56          | ~ (l1_pre_topc @ X36))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.36/0.56  thf(dt_k2_subset_1, axiom,
% 0.36/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.56  thf('6', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.56  thf('7', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.36/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf(d5_pre_topc, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.36/0.56             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X39 : $i, X40 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.36/0.56          | ~ (r2_hidden @ X39 @ (u1_pre_topc @ X40))
% 0.36/0.56          | (v3_pre_topc @ X39 @ X40)
% 0.36/0.56          | ~ (l1_pre_topc @ X40))),
% 0.36/0.56      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X0)
% 0.36/0.56          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.56          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0)
% 0.36/0.56          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['4', '9'])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.36/0.56  thf(t5_pre_topc, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ))).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (![X43 : $i]:
% 0.36/0.56         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X43))
% 0.36/0.56          | ~ (l1_pre_topc @ X43)
% 0.36/0.56          | ~ (v2_pre_topc @ X43))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_pre_topc])).
% 0.36/0.56  thf(t4_subset_1, axiom,
% 0.36/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X39 : $i, X40 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.36/0.56          | ~ (r2_hidden @ X39 @ (u1_pre_topc @ X40))
% 0.36/0.56          | (v3_pre_topc @ X39 @ X40)
% 0.36/0.56          | ~ (l1_pre_topc @ X40))),
% 0.36/0.56      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X0)
% 0.36/0.56          | (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.36/0.56          | ~ (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v2_pre_topc @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.56  thf(t30_tops_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.36/0.56             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X44 : $i, X45 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.36/0.56          | ~ (v3_pre_topc @ X44 @ X45)
% 0.36/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 0.36/0.56          | ~ (l1_pre_topc @ X45))),
% 0.36/0.56      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X0)
% 0.36/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.36/0.56             X0)
% 0.36/0.56          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.56  thf(d5_subset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i]:
% 0.36/0.56         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.36/0.56          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.56  thf(t3_boole, axiom,
% 0.36/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.56  thf('24', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.56  thf('25', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X0)
% 0.36/0.56          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.56          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['20', '25'])).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v2_pre_topc @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '26'])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.36/0.56  thf('29', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.36/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (![X46 : $i]:
% 0.36/0.56         (~ (v3_pre_topc @ X46 @ sk_A)
% 0.36/0.56          | ~ (v4_pre_topc @ X46 @ sk_A)
% 0.36/0.56          | ~ (r2_hidden @ sk_B_2 @ X46)
% 0.36/0.56          | (r2_hidden @ X46 @ sk_C_1)
% 0.36/0.56          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('31', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X46 : $i]:
% 0.36/0.56         (~ (v3_pre_topc @ X46 @ sk_A)
% 0.36/0.56          | ~ (v4_pre_topc @ X46 @ sk_A)
% 0.36/0.56          | ~ (r2_hidden @ sk_B_2 @ X46)
% 0.36/0.56          | (r2_hidden @ X46 @ k1_xboole_0)
% 0.36/0.56          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.56        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['29', '32'])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.56        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['28', '33'])).
% 0.36/0.56  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.56        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.56        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['11', '37'])).
% 0.36/0.56  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.56        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['3', '41'])).
% 0.36/0.56  thf(t7_ordinal1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.56  thf('43', plain,
% 0.36/0.56      (![X12 : $i, X13 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.56  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.56  thf('46', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.56  thf(fc2_struct_0, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      (![X42 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X42))
% 0.36/0.56          | ~ (l1_struct_0 @ X42)
% 0.36/0.56          | (v2_struct_0 @ X42))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.56  thf('48', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.56  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(dt_l1_pre_topc, axiom,
% 0.36/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      (![X41 : $i]: ((l1_struct_0 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.56  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.56  thf('52', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('demod', [status(thm)], ['48', '51'])).
% 0.36/0.56  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
