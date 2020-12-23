%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TbrA1RlI5w

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:06 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 159 expanded)
%              Number of leaves         :   58 (  79 expanded)
%              Depth                    :   21
%              Number of atoms          :  741 (1760 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X35: $i] :
      ( ~ ( v2_pre_topc @ X35 )
      | ( r2_hidden @ ( u1_struct_0 @ X35 ) @ ( u1_pre_topc @ X35 ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r2_hidden @ X39 @ ( u1_pre_topc @ X40 ) )
      | ( v3_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ! [X42: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X42 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X38: $i] :
      ( ( ( k2_struct_0 @ X38 )
        = ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('16',plain,(
    ! [X44: $i] :
      ( ~ ( v3_pre_topc @ X44 @ sk_A )
      | ~ ( v4_pre_topc @ X44 @ sk_A )
      | ~ ( r2_hidden @ sk_B_4 @ X44 )
      | ( r2_hidden @ X44 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X44: $i] :
      ( ~ ( v3_pre_topc @ X44 @ sk_A )
      | ~ ( v4_pre_topc @ X44 @ sk_A )
      | ~ ( r2_hidden @ sk_B_4 @ X44 )
      | ( r2_hidden @ X44 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
    ! [X41: $i] :
      ( ( l1_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
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

thf('38',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('39',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','42'])).

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

thf('44',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( sk_B_3 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_3 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_3 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B_3 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','53'])).

thf('55',plain,(
    ! [X43: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_3 @ X43 ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TbrA1RlI5w
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 364 iterations in 0.204s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.66  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.46/0.66  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.46/0.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.66  thf(sk_B_3_type, type, sk_B_3: $i > $i).
% 0.46/0.66  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.46/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(sk_B_4_type, type, sk_B_4: $i).
% 0.46/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.66  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(t28_connsp_2, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @
% 0.46/0.66                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66               ( ~( ( ![D:$i]:
% 0.46/0.66                      ( ( m1_subset_1 @
% 0.46/0.66                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                        ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.66                          ( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.66                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.46/0.66                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.66            ( l1_pre_topc @ A ) ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( m1_subset_1 @
% 0.46/0.66                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66                  ( ~( ( ![D:$i]:
% 0.46/0.66                         ( ( m1_subset_1 @
% 0.46/0.66                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                           ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.66                             ( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.66                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.46/0.66                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.46/0.66  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t9_mcart_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ~( ( r2_hidden @ B @ A ) & 
% 0.46/0.66                 ( ![C:$i,D:$i]:
% 0.46/0.66                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.46/0.66                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X10 : $i]:
% 0.46/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.46/0.66  thf('2', plain, ((m1_subset_1 @ sk_B_4 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t2_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.66       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         ((r2_hidden @ X3 @ X4)
% 0.46/0.66          | (v1_xboole_0 @ X4)
% 0.46/0.66          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf(d1_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ( v2_pre_topc @ A ) <=>
% 0.46/0.66         ( ( ![B:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ![C:$i]:
% 0.46/0.66                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.66                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.46/0.66                     ( r2_hidden @
% 0.46/0.66                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.46/0.66                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.46/0.66           ( ![B:$i]:
% 0.46/0.66             ( ( m1_subset_1 @
% 0.46/0.66                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.46/0.66                 ( r2_hidden @
% 0.46/0.66                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.46/0.66                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.46/0.66           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_2, axiom,
% 0.46/0.66    (![B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.46/0.66       ( ( m1_subset_1 @
% 0.46/0.66           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.46/0.66  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_4, axiom,
% 0.46/0.66    (![B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.46/0.66       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.46/0.66         ( r2_hidden @
% 0.46/0.66           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_6, axiom,
% 0.46/0.66    (![B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.46/0.66       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_8, axiom,
% 0.46/0.66    (![C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.46/0.66       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.46/0.66  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_10, axiom,
% 0.46/0.66    (![C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.46/0.66       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.46/0.66         ( r2_hidden @
% 0.46/0.66           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_12, axiom,
% 0.46/0.66    (![C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.46/0.66       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.66         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_13, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ( v2_pre_topc @ A ) <=>
% 0.46/0.66         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.66           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.46/0.66           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X35 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X35)
% 0.46/0.66          | (r2_hidden @ (u1_struct_0 @ X35) @ (u1_pre_topc @ X35))
% 0.46/0.66          | ~ (l1_pre_topc @ X35))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.46/0.66  thf(dt_k2_subset_1, axiom,
% 0.46/0.66    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.46/0.66  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.66  thf('7', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.66  thf('8', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(d5_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.66             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X39 : $i, X40 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.46/0.66          | ~ (r2_hidden @ X39 @ (u1_pre_topc @ X40))
% 0.46/0.66          | (v3_pre_topc @ X39 @ X40)
% 0.46/0.66          | ~ (l1_pre_topc @ X40))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.66          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '10'])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.66  thf(fc4_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X42 : $i]:
% 0.46/0.66         ((v4_pre_topc @ (k2_struct_0 @ X42) @ X42)
% 0.46/0.66          | ~ (l1_pre_topc @ X42)
% 0.46/0.66          | ~ (v2_pre_topc @ X42))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.46/0.66  thf(d3_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X38 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X38) = (u1_struct_0 @ X38)) | ~ (l1_struct_0 @ X38))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('15', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X44 : $i]:
% 0.46/0.66         (~ (v3_pre_topc @ X44 @ sk_A)
% 0.46/0.66          | ~ (v4_pre_topc @ X44 @ sk_A)
% 0.46/0.66          | ~ (r2_hidden @ sk_B_4 @ X44)
% 0.46/0.66          | (r2_hidden @ X44 @ sk_C_1)
% 0.46/0.66          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('17', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X44 : $i]:
% 0.46/0.66         (~ (v3_pre_topc @ X44 @ sk_A)
% 0.46/0.66          | ~ (v4_pre_topc @ X44 @ sk_A)
% 0.46/0.66          | ~ (r2_hidden @ sk_B_4 @ X44)
% 0.46/0.66          | (r2_hidden @ X44 @ k1_xboole_0)
% 0.46/0.66          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.46/0.66        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.66        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['15', '18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.66        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['14', '19'])).
% 0.46/0.66  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_l1_pre_topc, axiom,
% 0.46/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X41 : $i]: ((l1_struct_0 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.66  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.46/0.66        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.66        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '23'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      ((~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.46/0.66        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['13', '24'])).
% 0.46/0.66  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.46/0.66        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['12', '28'])).
% 0.46/0.66  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((~ (r2_hidden @ sk_B_4 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '32'])).
% 0.46/0.66  thf(t7_ordinal1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.66  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.66  thf('37', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X10 : $i]:
% 0.46/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.46/0.66  thf('39', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(t5_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.66          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X5 @ X6)
% 0.46/0.66          | ~ (v1_xboole_0 @ X7)
% 0.46/0.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['38', '41'])).
% 0.46/0.66  thf('43', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['37', '42'])).
% 0.46/0.66  thf(rc3_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ?[B:$i]:
% 0.46/0.66         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.46/0.66           ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.66           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X43 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (sk_B_3 @ X43) @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.46/0.66          | ~ (l1_pre_topc @ X43)
% 0.46/0.66          | ~ (v2_pre_topc @ X43)
% 0.46/0.66          | (v2_struct_0 @ X43))),
% 0.46/0.66      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X5 @ X6)
% 0.46/0.66          | ~ (v1_xboole_0 @ X7)
% 0.46/0.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((v2_struct_0 @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.46/0.66          | ~ (r2_hidden @ X1 @ (sk_B_3 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | ~ (r2_hidden @ X0 @ (sk_B_3 @ sk_A))
% 0.46/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66          | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['43', '46'])).
% 0.46/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.66  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (sk_B_3 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.46/0.66  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_3 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain, (((sk_B_3 @ sk_A) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '53'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X43 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (sk_B_3 @ X43))
% 0.46/0.66          | ~ (l1_pre_topc @ X43)
% 0.46/0.66          | ~ (v2_pre_topc @ X43)
% 0.46/0.66          | (v2_struct_0 @ X43))),
% 0.46/0.66      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.66  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('60', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.46/0.66  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
