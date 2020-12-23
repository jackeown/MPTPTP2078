%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KeOz3lpbcu

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:06 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 172 expanded)
%              Number of leaves         :   59 (  84 expanded)
%              Depth                    :   21
%              Number of atoms          :  748 (1818 expanded)
%              Number of equality atoms :   14 (  44 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_5_type,type,(
    sk_B_5: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

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
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B_5 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_5 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('16',plain,(
    ! [X47: $i] :
      ( ~ ( v3_pre_topc @ X47 @ sk_A )
      | ~ ( v4_pre_topc @ X47 @ sk_A )
      | ~ ( r2_hidden @ sk_B_5 @ X47 )
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
      | ~ ( r2_hidden @ sk_B_5 @ X47 )
      | ( r2_hidden @ X47 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_5 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_5 @ ( u1_struct_0 @ sk_A ) )
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
    | ~ ( r2_hidden @ sk_B_5 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_5 @ ( u1_struct_0 @ sk_A ) )
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
    | ~ ( r2_hidden @ sk_B_5 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B_5 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B_5 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','32'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

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

thf('46',plain,(
    ! [X46: $i] :
      ( ( m1_subset_1 @ ( sk_B_4 @ X46 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_4 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_4 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_4 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_4 @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B_4 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','55'])).

thf('57',plain,(
    ! [X46: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_4 @ X46 ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KeOz3lpbcu
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 312 iterations in 0.180s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.64  thf(sk_B_5_type, type, sk_B_5: $i).
% 0.45/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.64  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.64  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.64  thf(sk_B_4_type, type, sk_B_4: $i > $i).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.64  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.64  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.64  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.45/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.64  thf(t28_connsp_2, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( m1_subset_1 @
% 0.45/0.64                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64               ( ~( ( ![D:$i]:
% 0.45/0.64                      ( ( m1_subset_1 @
% 0.45/0.64                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64                        ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.64                          ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.64                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.64                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.64            ( l1_pre_topc @ A ) ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64              ( ![C:$i]:
% 0.45/0.64                ( ( m1_subset_1 @
% 0.45/0.64                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64                  ( ~( ( ![D:$i]:
% 0.45/0.64                         ( ( m1_subset_1 @
% 0.45/0.64                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64                           ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.64                             ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.64                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.64                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.45/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t9_mcart_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.64                 ( ![C:$i,D:$i]:
% 0.45/0.64                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.45/0.64                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X13 : $i]:
% 0.45/0.64         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.45/0.64  thf('2', plain, ((m1_subset_1 @ sk_B_5 @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t2_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.64       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i]:
% 0.45/0.64         ((r2_hidden @ X6 @ X7)
% 0.45/0.64          | (v1_xboole_0 @ X7)
% 0.45/0.64          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ sk_B_5 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.64  thf(d1_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ( v2_pre_topc @ A ) <=>
% 0.45/0.64         ( ( ![B:$i]:
% 0.45/0.64             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64               ( ![C:$i]:
% 0.45/0.64                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.64                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.45/0.64                     ( r2_hidden @
% 0.45/0.64                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.45/0.64                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.45/0.64           ( ![B:$i]:
% 0.45/0.64             ( ( m1_subset_1 @
% 0.45/0.64                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.45/0.64                 ( r2_hidden @
% 0.45/0.64                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.45/0.64                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.45/0.64           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_2, axiom,
% 0.45/0.64    (![B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.45/0.64       ( ( m1_subset_1 @
% 0.45/0.64           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.45/0.64  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_4, axiom,
% 0.45/0.64    (![B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.45/0.64       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.45/0.64         ( r2_hidden @
% 0.45/0.64           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_6, axiom,
% 0.45/0.64    (![B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.45/0.64       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_8, axiom,
% 0.45/0.64    (![C:$i,B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.45/0.64       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.45/0.64  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_10, axiom,
% 0.45/0.64    (![C:$i,B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.45/0.64       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.45/0.64         ( r2_hidden @
% 0.45/0.64           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_12, axiom,
% 0.45/0.64    (![C:$i,B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.45/0.64       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.64         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_13, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ( v2_pre_topc @ A ) <=>
% 0.45/0.64         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.45/0.64           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.45/0.64           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X38 : $i]:
% 0.45/0.64         (~ (v2_pre_topc @ X38)
% 0.45/0.64          | (r2_hidden @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))
% 0.45/0.64          | ~ (l1_pre_topc @ X38))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.45/0.64  thf(dt_k2_subset_1, axiom,
% 0.45/0.64    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.45/0.64  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.64  thf('7', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.64  thf('8', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.45/0.64      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf(d5_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.64             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X42 : $i, X43 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.45/0.64          | ~ (r2_hidden @ X42 @ (u1_pre_topc @ X43))
% 0.45/0.64          | (v3_pre_topc @ X42 @ X43)
% 0.45/0.64          | ~ (l1_pre_topc @ X43))),
% 0.45/0.64      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X0)
% 0.45/0.64          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.64          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X0)
% 0.45/0.64          | ~ (v2_pre_topc @ X0)
% 0.45/0.64          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['5', '10'])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.64          | ~ (v2_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.64  thf(fc4_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X45 : $i]:
% 0.45/0.64         ((v4_pre_topc @ (k2_struct_0 @ X45) @ X45)
% 0.45/0.64          | ~ (l1_pre_topc @ X45)
% 0.45/0.64          | ~ (v2_pre_topc @ X45))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.45/0.64  thf(d3_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X41 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('15', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.45/0.64      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X47 : $i]:
% 0.45/0.64         (~ (v3_pre_topc @ X47 @ sk_A)
% 0.45/0.64          | ~ (v4_pre_topc @ X47 @ sk_A)
% 0.45/0.64          | ~ (r2_hidden @ sk_B_5 @ X47)
% 0.45/0.64          | (r2_hidden @ X47 @ sk_C_1)
% 0.45/0.64          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('17', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X47 : $i]:
% 0.45/0.64         (~ (v3_pre_topc @ X47 @ sk_A)
% 0.45/0.64          | ~ (v4_pre_topc @ X47 @ sk_A)
% 0.45/0.64          | ~ (r2_hidden @ sk_B_5 @ X47)
% 0.45/0.64          | (r2_hidden @ X47 @ k1_xboole_0)
% 0.45/0.64          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.64        | ~ (r2_hidden @ sk_B_5 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '18'])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (r2_hidden @ sk_B_5 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '19'])).
% 0.45/0.64  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_l1_pre_topc, axiom,
% 0.45/0.64    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X44 : $i]: ((l1_struct_0 @ X44) | ~ (l1_pre_topc @ X44))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.64  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.64        | ~ (r2_hidden @ sk_B_5 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['20', '23'])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.64        | ~ (r2_hidden @ sk_B_5 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['13', '24'])).
% 0.45/0.64  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.64        | ~ (r2_hidden @ sk_B_5 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.64        | ~ (r2_hidden @ sk_B_5 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['12', '28'])).
% 0.45/0.64  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      ((~ (r2_hidden @ sk_B_5 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['4', '32'])).
% 0.45/0.64  thf(d1_xboole_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.64  thf('36', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.64  thf(t7_ordinal1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X11 : $i, X12 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.45/0.64      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.64  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['36', '39'])).
% 0.45/0.64  thf('41', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['35', '40'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X13 : $i]:
% 0.45/0.64         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.64  thf('45', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['41', '44'])).
% 0.45/0.64  thf(rc3_tops_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( ?[B:$i]:
% 0.45/0.64         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.45/0.64           ( ~( v1_xboole_0 @ B ) ) & 
% 0.45/0.64           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X46 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (sk_B_4 @ X46) @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.45/0.64          | ~ (l1_pre_topc @ X46)
% 0.45/0.64          | ~ (v2_pre_topc @ X46)
% 0.45/0.64          | (v2_struct_0 @ X46))),
% 0.45/0.64      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.45/0.64  thf(t5_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.64          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X8 @ X9)
% 0.45/0.64          | ~ (v1_xboole_0 @ X10)
% 0.45/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((v2_struct_0 @ X0)
% 0.45/0.64          | ~ (v2_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0)
% 0.45/0.64          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.64          | ~ (r2_hidden @ X1 @ (sk_B_4 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (sk_B_4 @ sk_A))
% 0.45/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.64          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.64          | (v2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '48'])).
% 0.45/0.64  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['36', '39'])).
% 0.45/0.64  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ (sk_B_4 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.45/0.64  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_4 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('56', plain, (((sk_B_4 @ sk_A) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '55'])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      (![X46 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (sk_B_4 @ X46))
% 0.45/0.64          | ~ (l1_pre_topc @ X46)
% 0.45/0.64          | ~ (v2_pre_topc @ X46)
% 0.45/0.64          | (v2_struct_0 @ X46))),
% 0.45/0.64      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.64        | (v2_struct_0 @ sk_A)
% 0.45/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.64  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['36', '39'])).
% 0.45/0.64  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('62', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.64      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.45/0.64  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
