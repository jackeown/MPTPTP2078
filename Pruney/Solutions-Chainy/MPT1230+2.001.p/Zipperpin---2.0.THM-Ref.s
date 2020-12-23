%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJwa7osANt

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 261 expanded)
%              Number of leaves         :   27 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          : 1442 (4943 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t39_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ~ ( ( v3_pre_topc @ D @ A )
                        & ( r2_hidden @ C @ D )
                        & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ~ ( ( v3_pre_topc @ D @ A )
                          & ( r2_hidden @ C @ D )
                          & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_tops_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X17 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ X17 )
      | ~ ( r1_xboole_0 @ sk_B @ X17 )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d13_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( r1_xboole_0 @ B @ E )
                              & ( r2_hidden @ D @ E )
                              & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( v3_pre_topc @ E @ A )
        & ( r2_hidden @ D @ E )
        & ( r1_xboole_0 @ B @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X9
       != ( k2_pre_topc @ X8 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X11 @ X7 @ X8 ) @ X11 @ X7 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X8 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X8 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X11 @ X7 @ X8 ) @ X11 @ X7 @ X8 )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v3_pre_topc @ X2 @ X3 )
      | ~ ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X5 @ X2 )
      | ~ ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('29',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X9
       != ( k2_pre_topc @ X8 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ( m1_subset_1 @ ( sk_E_1 @ X11 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X8 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X11 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,
    ( ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) )
   <= ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('38',plain,
    ( ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ),
    inference('sup-',[status(thm)],['24','40'])).

thf('42',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('45',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X17: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X17 )
        | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ! [X17: $i] :
          ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X17 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X17 )
          | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('50',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ! [X17: $i] :
          ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X17 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X17 )
          | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ! [X17: $i] :
          ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X17 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X17 )
          | ~ ( r1_xboole_0 @ sk_B @ X17 ) ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ! [X17: $i] :
          ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X17 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X17 )
          | ~ ( r1_xboole_0 @ sk_B @ X17 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['47'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('60',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
   <= ( r2_hidden @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['47'])).

thf('63',plain,(
    ! [X2: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v3_pre_topc @ sk_D_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_D_1 )
        | ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_D_1 ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X9
       != ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X7 @ X8 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    ! [X7: $i,X8: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X8 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( zip_tseitin_0 @ sk_D_1 @ X0 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,
    ( ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','78'])).

thf('80',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','57','58','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJwa7osANt
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 129 iterations in 0.095s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.55  thf(t39_tops_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.55                 ( ![D:$i]:
% 0.20/0.55                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                     ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 0.20/0.55                          ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55            ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55                  ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.55                    ( ![D:$i]:
% 0.20/0.55                      ( ( m1_subset_1 @
% 0.20/0.55                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                        ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 0.20/0.55                             ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t39_tops_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (((r2_hidden @ sk_C @ sk_D_1)
% 0.20/0.55        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (((r2_hidden @ sk_C @ sk_D_1)) | 
% 0.20/0.55       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (((v3_pre_topc @ sk_D_1 @ sk_A)
% 0.20/0.55        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((v3_pre_topc @ sk_D_1 @ sk_A)) | 
% 0.20/0.55       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.55       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['4'])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X17 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.55          | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.55          | ~ (r1_xboole_0 @ sk_B @ X17)
% 0.20/0.55          | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((![X17 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55           | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.55           | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.55           | ~ (r1_xboole_0 @ sk_B @ X17))) | 
% 0.20/0.55       ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('8', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t2_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ X1)
% 0.20/0.55          | (v1_xboole_0 @ X1)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k2_pre_topc, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55       ( m1_subset_1 @
% 0.20/0.55         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X13)
% 0.20/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.55          | (m1_subset_1 @ (k2_pre_topc @ X13 @ X14) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf(d13_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.55                 ( ![D:$i]:
% 0.20/0.55                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55                     ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55                       ( ![E:$i]:
% 0.20/0.55                         ( ( m1_subset_1 @
% 0.20/0.55                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                           ( ~( ( r1_xboole_0 @ B @ E ) & 
% 0.20/0.55                                ( r2_hidden @ D @ E ) & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_2, axiom,
% 0.20/0.55    (![E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.20/0.55       ( ( v3_pre_topc @ E @ A ) & ( r2_hidden @ D @ E ) & 
% 0.20/0.55         ( r1_xboole_0 @ B @ E ) ) ))).
% 0.20/0.55  thf(zf_stmt_3, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.55                 ( ![D:$i]:
% 0.20/0.55                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55                     ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55                       ( ![E:$i]:
% 0.20/0.55                         ( ( m1_subset_1 @
% 0.20/0.55                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                           ( ~( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ((X9) != (k2_pre_topc @ X8 @ X7))
% 0.20/0.55          | (r2_hidden @ X11 @ X9)
% 0.20/0.55          | (zip_tseitin_0 @ (sk_E_1 @ X11 @ X7 @ X8) @ X11 @ X7 @ X8)
% 0.20/0.55          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (l1_pre_topc @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ (k2_pre_topc @ X8 @ X7) @ 
% 0.20/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.55          | (zip_tseitin_0 @ (sk_E_1 @ X11 @ X7 @ X8) @ X11 @ X7 @ X8)
% 0.20/0.55          | (r2_hidden @ X11 @ (k2_pre_topc @ X8 @ X7))
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.55          | (zip_tseitin_0 @ (sk_E_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.55          | (zip_tseitin_0 @ (sk_E_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B @ sk_A)
% 0.20/0.55        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         ((v3_pre_topc @ X2 @ X3) | ~ (zip_tseitin_0 @ X2 @ X4 @ X5 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (v3_pre_topc @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B @ sk_A)
% 0.20/0.55        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X5 @ X2) | ~ (zip_tseitin_0 @ X2 @ X4 @ X5 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r1_xboole_0 @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ((X9) != (k2_pre_topc @ X8 @ X7))
% 0.20/0.55          | (r2_hidden @ X11 @ X9)
% 0.20/0.55          | (m1_subset_1 @ (sk_E_1 @ X11 @ X7 @ X8) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (l1_pre_topc @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ (k2_pre_topc @ X8 @ X7) @ 
% 0.20/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.55          | (m1_subset_1 @ (sk_E_1 @ X11 @ X7 @ X8) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | (r2_hidden @ X11 @ (k2_pre_topc @ X8 @ X7))
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.55          | (m1_subset_1 @ (sk_E_1 @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.55          | (m1_subset_1 @ (sk_E_1 @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (m1_subset_1 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['28', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((![X17 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55           | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.55           | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.55           | ~ (r1_xboole_0 @ sk_B @ X17)))
% 0.20/0.55         <= ((![X17 : $i]:
% 0.20/0.55                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.55                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      ((((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55         | ~ (r1_xboole_0 @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.55         | ~ (r2_hidden @ sk_C @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.55         | ~ (v3_pre_topc @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)))
% 0.20/0.55         <= ((![X17 : $i]:
% 0.20/0.55                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56         | ~ (v3_pre_topc @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56         | ~ (r2_hidden @ sk_C @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.56         <= ((![X17 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (((~ (r2_hidden @ sk_C @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.56         | ~ (v3_pre_topc @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= ((![X17 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56         | ~ (r2_hidden @ sk_C @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.20/0.56         <= ((![X17 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '40'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (((~ (r2_hidden @ sk_C @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= ((![X17 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56        | (zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B @ sk_A)
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.56         ((r2_hidden @ X4 @ X2) | ~ (zip_tseitin_0 @ X2 @ X4 @ X5 @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56        | (r2_hidden @ sk_C @ (sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.56         <= ((![X17 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('clc', [status(thm)], ['42', '45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (((r1_xboole_0 @ sk_B @ sk_D_1)
% 0.20/0.56        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.56      inference('split', [status(esa)], ['47'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.56             (![X17 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['46', '48'])).
% 0.20/0.56  thf(fc2_struct_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (![X16 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.20/0.56          | ~ (l1_struct_0 @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.56             (![X17 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_l1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.56  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.56             (![X17 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56                 | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56                 | ~ (r1_xboole_0 @ sk_B @ X17))))),
% 0.20/0.56      inference('demod', [status(thm)], ['51', '54'])).
% 0.20/0.56  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      (~
% 0.20/0.56       (![X17 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56           | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.20/0.56           | ~ (r2_hidden @ sk_C @ X17)
% 0.20/0.56           | ~ (r1_xboole_0 @ sk_B @ X17))) | 
% 0.20/0.56       ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (((r1_xboole_0 @ sk_B @ sk_D_1)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['47'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ sk_D_1)) <= (((r2_hidden @ sk_C @ sk_D_1)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      (((v3_pre_topc @ sk_D_1 @ sk_A)) <= (((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      (((r1_xboole_0 @ sk_B @ sk_D_1)) <= (((r1_xboole_0 @ sk_B @ sk_D_1)))),
% 0.20/0.56      inference('split', [status(esa)], ['47'])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      (![X2 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X2 @ X4 @ X5 @ X6)
% 0.20/0.56          | ~ (r1_xboole_0 @ X5 @ X2)
% 0.20/0.56          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.56          | ~ (v3_pre_topc @ X2 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      ((![X0 : $i, X1 : $i]:
% 0.20/0.56          (~ (v3_pre_topc @ sk_D_1 @ X0)
% 0.20/0.56           | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.20/0.56           | (zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0)))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_B @ sk_D_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((zip_tseitin_0 @ sk_D_1 @ X0 @ sk_B @ sk_A)
% 0.20/0.56           | ~ (r2_hidden @ X0 @ sk_D_1)))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_B @ sk_D_1)) & ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['61', '64'])).
% 0.20/0.56  thf('66', plain,
% 0.20/0.56      (((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.56             ((r2_hidden @ sk_C @ sk_D_1)) & 
% 0.20/0.56             ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['60', '65'])).
% 0.20/0.56  thf('67', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.56         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.56      inference('split', [status(esa)], ['6'])).
% 0.20/0.56  thf('68', plain,
% 0.20/0.56      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('70', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.56          | ((X9) != (k2_pre_topc @ X8 @ X7))
% 0.20/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X10 @ X11 @ X7 @ X8)
% 0.20/0.56          | ~ (r2_hidden @ X11 @ X9)
% 0.20/0.56          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.56          | ~ (l1_pre_topc @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X8)
% 0.20/0.56          | ~ (m1_subset_1 @ (k2_pre_topc @ X8 @ X7) @ 
% 0.20/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.56          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.56          | ~ (r2_hidden @ X11 @ (k2_pre_topc @ X8 @ X7))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X10 @ X11 @ X7 @ X8)
% 0.20/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.56  thf('72', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X0 @ X1 @ sk_B @ sk_A)
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['69', '71'])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X0 @ X1 @ sk_B @ sk_A)
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56           | ~ (zip_tseitin_0 @ sk_D_1 @ X0 @ sk_B @ sk_A)))
% 0.20/0.56         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['68', '75'])).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      (((~ (zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A)
% 0.20/0.56         | ~ (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.56             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['67', '76'])).
% 0.20/0.56  thf('78', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.20/0.56         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.56             ((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.56             ((r2_hidden @ sk_C @ sk_D_1)) & 
% 0.20/0.56             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.20/0.56             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['66', '77'])).
% 0.20/0.56  thf('79', plain,
% 0.20/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.56             ((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.56             ((r2_hidden @ sk_C @ sk_D_1)) & 
% 0.20/0.56             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.20/0.56             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['59', '78'])).
% 0.20/0.56  thf('80', plain,
% 0.20/0.56      (![X16 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.20/0.56          | ~ (l1_struct_0 @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.56  thf('81', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.56         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.56             ((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.56             ((r2_hidden @ sk_C @ sk_D_1)) & 
% 0.20/0.56             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.20/0.56             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.56  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A))
% 0.20/0.56         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.56             ((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.56             ((r2_hidden @ sk_C @ sk_D_1)) & 
% 0.20/0.56             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.20/0.56             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.20/0.56  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      (~ ((r1_xboole_0 @ sk_B @ sk_D_1)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) | 
% 0.20/0.56       ~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.56       ~ ((v3_pre_topc @ sk_D_1 @ sk_A)) | ~ ((r2_hidden @ sk_C @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.56  thf('86', plain, ($false),
% 0.20/0.56      inference('sat_resolution*', [status(thm)],
% 0.20/0.56                ['1', '3', '5', '7', '57', '58', '85'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
