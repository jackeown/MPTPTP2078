%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4w03YKZYE5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:06 EST 2020

% Result     : Theorem 5.65s
% Output     : Refutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :  329 (3291 expanded)
%              Number of leaves         :   50 (1019 expanded)
%              Depth                    :   36
%              Number of atoms          : 3804 (41603 expanded)
%              Number of equality atoms :  227 (2528 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t80_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( C != k1_xboole_0 )
                    & ( v3_pre_topc @ C @ A )
                    & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v1_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( C != k1_xboole_0 )
                      & ( v3_pre_topc @ C @ A )
                      & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_tops_1])).

thf('0',plain,(
    ! [X49: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X49 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_B @ X49 )
      | ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X32 @ X30 @ X31 ) @ X32 )
      | ( zip_tseitin_0 @ ( sk_E @ X32 @ X30 @ X31 ) @ ( sk_D @ X32 @ X30 @ X31 ) @ X30 @ X31 )
      | ( X32
        = ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r2_hidden @ ( sk_D @ X32 @ X30 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ( X32
        = ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ X28 @ X25 )
      | ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ sk_B @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X32 @ X30 @ X31 ) @ X32 )
      | ( m1_subset_1 @ ( sk_E @ X32 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X32
        = ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,
    ( ( ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','17'])).

thf('36',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v3_pre_topc @ X25 @ X26 )
      | ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(clc,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','17'])).

thf('40',plain,
    ( ( ( zip_tseitin_0 @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(clc,[status(thm)],['34','37'])).

thf('43',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('44',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_pre_topc @ X45 @ X44 )
       != ( k2_struct_0 @ X45 ) )
      | ( v1_tops_1 @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('56',plain,(
    ! [X37: $i] :
      ( ( l1_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v1_tops_1 @ X44 @ X45 )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = ( k2_struct_0 @ X45 ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ sk_B )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup+',[status(thm)],['45','65'])).

thf('67',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('70',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('71',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 ) @ X48 )
      | ( v4_pre_topc @ X47 @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('75',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('78',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('84',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','89','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['67','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('102',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('103',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v4_pre_topc @ X38 @ X39 )
      | ( ( k2_pre_topc @ X39 @ X38 )
        = X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('112',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('113',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 ) @ X48 )
      | ( v4_pre_topc @ X47 @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('122',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v4_pre_topc @ X38 @ X39 )
      | ( ( k2_pre_topc @ X39 @ X38 )
        = X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup+',[status(thm)],['110','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('129',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup+',[status(thm)],['109','129'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('133',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ k1_xboole_0 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(demod,[status(thm)],['41','131','132'])).

thf('134',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X25 )
      | ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('135',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('138',plain,(
    ! [X46: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X46 ) @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('139',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('140',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('141',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 ) @ X48 )
      | ( v4_pre_topc @ X47 @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('144',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['142','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['137','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('158',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('159',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v4_pre_topc @ X38 @ X39 )
      | ( ( k2_pre_topc @ X39 @ X38 )
        = X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( ( k2_pre_topc @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['156','161'])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('166',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t54_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ( ~ ( v2_struct_0 @ A )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ~ ( ( v3_pre_topc @ D @ A )
                          & ( r2_hidden @ C @ D )
                          & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) )).

thf('167',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( r2_hidden @ X42 @ ( k2_pre_topc @ X41 @ X40 ) )
      | ~ ( r1_xboole_0 @ X40 @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( v3_pre_topc @ X43 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('170',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('172',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['168','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['164','176'])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('181',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v4_pre_topc @ X47 @ X48 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 ) @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k5_xboole_0 @ X1 @ X1 ) ) @ X0 )
      | ~ ( v4_pre_topc @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['188','191'])).

thf('193',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['179','192'])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['177','178','195'])).

thf('197',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('198',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( m1_subset_1 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['196','199'])).

thf('201',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('202',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['200','203'])).

thf('205',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(clc,[status(thm)],['135','204'])).

thf('206',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('207',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ! [X49: $i] :
        ( ( X49 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X49 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X49 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['209'])).

thf('211',plain,
    ( ~ ! [X49: $i] :
          ( ( X49 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X49 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X49 ) )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['208','210'])).

thf('212',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['209'])).

thf('213',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['213'])).

thf('215',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['215'])).

thf('217',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['217'])).

thf('219',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['217'])).

thf('220',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('221',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r2_hidden @ ( sk_D @ X32 @ X30 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ( X32
        = ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['219','222'])).

thf('224',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['162','163'])).

thf('225',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['193','194'])).

thf('228',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['173'])).

thf('229',plain,(
    ! [X25: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X29 )
      | ~ ( r1_xboole_0 @ X28 @ X25 )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( v3_pre_topc @ X25 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('230',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['227','230'])).

thf('232',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['226','231'])).

thf('233',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('234',plain,(
    ! [X30: $i,X31: $i,X32: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r2_hidden @ ( sk_D @ X32 @ X30 @ X31 ) @ X32 )
      | ~ ( zip_tseitin_0 @ X35 @ ( sk_D @ X32 @ X30 @ X31 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X32
        = ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['232','235'])).

thf('237',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('238',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['162','163'])).

thf('239',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['217'])).

thf('240',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['236','237','238','239','240'])).

thf('242',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['213'])).

thf('244',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['209'])).

thf('245',plain,(
    ! [X25: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X29 )
      | ~ ( r1_xboole_0 @ X28 @ X25 )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( v3_pre_topc @ X25 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('246',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v3_pre_topc @ sk_C @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_C )
        | ( zip_tseitin_0 @ sk_C @ X1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['243','246'])).

thf('248',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_B @ sk_A ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['242','247'])).

thf('249',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['217'])).

thf('250',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('251',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('252',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('254',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X32
       != ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X30 @ X31 )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( r2_hidden @ X34 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('255',plain,(
    ! [X30: $i,X31: $i,X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r2_hidden @ X34 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r2_hidden @ X34 @ ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_pre_topc @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['253','255'])).

thf('257',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['252','256'])).

thf('258',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('259',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('261',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('263',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['257','258','259','260','261','262'])).

thf('264',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['249','263'])).

thf('265',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['248','264'])).

thf('266',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('267',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('269',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('270',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['268','269'])).

thf('271',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('272',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['267','272'])).

thf('274',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['215'])).

thf('275',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','211','212','214','216','218','276'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4w03YKZYE5
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:11:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.65/5.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.65/5.85  % Solved by: fo/fo7.sh
% 5.65/5.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.65/5.85  % done 11862 iterations in 5.385s
% 5.65/5.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.65/5.85  % SZS output start Refutation
% 5.65/5.85  thf(sk_C_type, type, sk_C: $i).
% 5.65/5.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.65/5.85  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 5.65/5.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.65/5.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 5.65/5.85  thf(sk_B_type, type, sk_B: $i).
% 5.65/5.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.65/5.85  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.65/5.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.65/5.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.65/5.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.65/5.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.65/5.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.65/5.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.65/5.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.65/5.85  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.65/5.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.65/5.85  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.65/5.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.65/5.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.65/5.85  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.65/5.85  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.65/5.85  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 5.65/5.85  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.65/5.85  thf(sk_A_type, type, sk_A: $i).
% 5.65/5.85  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.65/5.85  thf(t80_tops_1, conjecture,
% 5.65/5.85    (![A:$i]:
% 5.65/5.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.65/5.85       ( ![B:$i]:
% 5.65/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85           ( ( v1_tops_1 @ B @ A ) <=>
% 5.65/5.85             ( ![C:$i]:
% 5.65/5.85               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85                 ( ~( ( ( C ) != ( k1_xboole_0 ) ) & ( v3_pre_topc @ C @ A ) & 
% 5.65/5.85                      ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ))).
% 5.65/5.85  thf(zf_stmt_0, negated_conjecture,
% 5.65/5.85    (~( ![A:$i]:
% 5.65/5.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.65/5.85          ( ![B:$i]:
% 5.65/5.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85              ( ( v1_tops_1 @ B @ A ) <=>
% 5.65/5.85                ( ![C:$i]:
% 5.65/5.85                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85                    ( ~( ( ( C ) != ( k1_xboole_0 ) ) & 
% 5.65/5.85                         ( v3_pre_topc @ C @ A ) & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ) )),
% 5.65/5.85    inference('cnf.neg', [status(esa)], [t80_tops_1])).
% 5.65/5.85  thf('0', plain,
% 5.65/5.85      (![X49 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ((X49) = (k1_xboole_0))
% 5.65/5.85          | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85          | ~ (r1_xboole_0 @ sk_B @ X49)
% 5.65/5.85          | (v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('1', plain,
% 5.65/5.85      ((![X49 : $i]:
% 5.65/5.85          (((X49) = (k1_xboole_0))
% 5.65/5.85           | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85           | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85           | ~ (r1_xboole_0 @ sk_B @ X49))) | 
% 5.65/5.85       ((v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.85      inference('split', [status(esa)], ['0'])).
% 5.65/5.85  thf(dt_k2_subset_1, axiom,
% 5.65/5.85    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.65/5.85  thf('2', plain,
% 5.65/5.85      (![X13 : $i]: (m1_subset_1 @ (k2_subset_1 @ X13) @ (k1_zfmisc_1 @ X13))),
% 5.65/5.85      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.65/5.85  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.65/5.85  thf('3', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 5.65/5.85      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.65/5.85  thf('4', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.85      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.85  thf('5', plain,
% 5.65/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf(d13_pre_topc, axiom,
% 5.65/5.85    (![A:$i]:
% 5.65/5.85     ( ( l1_pre_topc @ A ) =>
% 5.65/5.85       ( ![B:$i]:
% 5.65/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85           ( ![C:$i]:
% 5.65/5.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 5.65/5.85                 ( ![D:$i]:
% 5.65/5.85                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 5.65/5.85                     ( ( r2_hidden @ D @ C ) <=>
% 5.65/5.85                       ( ![E:$i]:
% 5.65/5.85                         ( ( m1_subset_1 @
% 5.65/5.85                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85                           ( ~( ( r1_xboole_0 @ B @ E ) & 
% 5.65/5.85                                ( r2_hidden @ D @ E ) & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.65/5.85  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 5.65/5.85  thf(zf_stmt_2, axiom,
% 5.65/5.85    (![E:$i,D:$i,B:$i,A:$i]:
% 5.65/5.85     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 5.65/5.85       ( ( v3_pre_topc @ E @ A ) & ( r2_hidden @ D @ E ) & 
% 5.65/5.85         ( r1_xboole_0 @ B @ E ) ) ))).
% 5.65/5.85  thf(zf_stmt_3, axiom,
% 5.65/5.85    (![A:$i]:
% 5.65/5.85     ( ( l1_pre_topc @ A ) =>
% 5.65/5.85       ( ![B:$i]:
% 5.65/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85           ( ![C:$i]:
% 5.65/5.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 5.65/5.85                 ( ![D:$i]:
% 5.65/5.85                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 5.65/5.85                     ( ( r2_hidden @ D @ C ) <=>
% 5.65/5.85                       ( ![E:$i]:
% 5.65/5.85                         ( ( m1_subset_1 @
% 5.65/5.85                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85                           ( ~( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.65/5.85  thf('6', plain,
% 5.65/5.85      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.85          | ~ (r2_hidden @ (sk_D @ X32 @ X30 @ X31) @ X32)
% 5.65/5.85          | (zip_tseitin_0 @ (sk_E @ X32 @ X30 @ X31) @ 
% 5.65/5.85             (sk_D @ X32 @ X30 @ X31) @ X30 @ X31)
% 5.65/5.85          | ((X32) = (k2_pre_topc @ X31 @ X30))
% 5.65/5.85          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.85          | ~ (l1_pre_topc @ X31))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.65/5.85  thf('7', plain,
% 5.65/5.85      (![X0 : $i]:
% 5.65/5.85         (~ (l1_pre_topc @ sk_A)
% 5.65/5.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 5.65/5.85             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 5.65/5.85          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 5.65/5.85      inference('sup-', [status(thm)], ['5', '6'])).
% 5.65/5.85  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('9', plain,
% 5.65/5.85      (![X0 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 5.65/5.85             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 5.65/5.85          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 5.65/5.85      inference('demod', [status(thm)], ['7', '8'])).
% 5.65/5.85  thf('10', plain,
% 5.65/5.85      ((~ (r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85           (u1_struct_0 @ sk_A))
% 5.65/5.85        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 5.65/5.85        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 5.65/5.85      inference('sup-', [status(thm)], ['4', '9'])).
% 5.65/5.85  thf('11', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.85      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.85  thf('12', plain,
% 5.65/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('13', plain,
% 5.65/5.85      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.85          | (r2_hidden @ (sk_D @ X32 @ X30 @ X31) @ (u1_struct_0 @ X31))
% 5.65/5.85          | ((X32) = (k2_pre_topc @ X31 @ X30))
% 5.65/5.85          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.85          | ~ (l1_pre_topc @ X31))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.65/5.85  thf('14', plain,
% 5.65/5.85      (![X0 : $i]:
% 5.65/5.85         (~ (l1_pre_topc @ sk_A)
% 5.65/5.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.65/5.85      inference('sup-', [status(thm)], ['12', '13'])).
% 5.65/5.85  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('16', plain,
% 5.65/5.85      (![X0 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 5.65/5.85      inference('demod', [status(thm)], ['14', '15'])).
% 5.65/5.85  thf('17', plain,
% 5.65/5.85      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85         (u1_struct_0 @ sk_A))
% 5.65/5.85        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 5.65/5.85      inference('sup-', [status(thm)], ['11', '16'])).
% 5.65/5.85  thf('18', plain,
% 5.65/5.85      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 5.65/5.85      inference('clc', [status(thm)], ['10', '17'])).
% 5.65/5.85  thf('19', plain,
% 5.65/5.85      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.65/5.85         ((r1_xboole_0 @ X28 @ X25) | ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X26))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.65/5.85  thf('20', plain,
% 5.65/5.85      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A)))),
% 5.65/5.85      inference('sup-', [status(thm)], ['18', '19'])).
% 5.65/5.85  thf('21', plain,
% 5.65/5.85      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85         (u1_struct_0 @ sk_A))
% 5.65/5.85        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 5.65/5.85      inference('sup-', [status(thm)], ['11', '16'])).
% 5.65/5.85  thf('22', plain,
% 5.65/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('23', plain,
% 5.65/5.85      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.85          | ~ (r2_hidden @ (sk_D @ X32 @ X30 @ X31) @ X32)
% 5.65/5.85          | (m1_subset_1 @ (sk_E @ X32 @ X30 @ X31) @ 
% 5.65/5.85             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.85          | ((X32) = (k2_pre_topc @ X31 @ X30))
% 5.65/5.85          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.85          | ~ (l1_pre_topc @ X31))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.65/5.85  thf('24', plain,
% 5.65/5.85      (![X0 : $i]:
% 5.65/5.85         (~ (l1_pre_topc @ sk_A)
% 5.65/5.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 5.65/5.85             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 5.65/5.85      inference('sup-', [status(thm)], ['22', '23'])).
% 5.65/5.85  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('26', plain,
% 5.65/5.85      (![X0 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 5.65/5.85             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 5.65/5.85      inference('demod', [status(thm)], ['24', '25'])).
% 5.65/5.85  thf('27', plain,
% 5.65/5.85      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.65/5.85             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.65/5.85      inference('sup-', [status(thm)], ['21', '26'])).
% 5.65/5.85  thf('28', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.85      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.85  thf('29', plain,
% 5.65/5.85      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 5.65/5.85      inference('demod', [status(thm)], ['27', '28'])).
% 5.65/5.85  thf('30', plain,
% 5.65/5.85      (((m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 5.65/5.85      inference('simplify', [status(thm)], ['29'])).
% 5.65/5.85  thf('31', plain,
% 5.65/5.85      ((![X49 : $i]:
% 5.65/5.85          (((X49) = (k1_xboole_0))
% 5.65/5.85           | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85           | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85           | ~ (r1_xboole_0 @ sk_B @ X49)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('split', [status(esa)], ['0'])).
% 5.65/5.85  thf('32', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | ~ (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A))
% 5.65/5.85         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 5.65/5.85         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('sup-', [status(thm)], ['30', '31'])).
% 5.65/5.85  thf('33', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 5.65/5.85         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 5.65/5.85         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('sup-', [status(thm)], ['20', '32'])).
% 5.65/5.85  thf('34', plain,
% 5.65/5.85      (((~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 5.65/5.85         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 5.65/5.85         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('simplify', [status(thm)], ['33'])).
% 5.65/5.85  thf('35', plain,
% 5.65/5.85      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 5.65/5.85      inference('clc', [status(thm)], ['10', '17'])).
% 5.65/5.85  thf('36', plain,
% 5.65/5.85      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.65/5.85         ((v3_pre_topc @ X25 @ X26) | ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X26))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.65/5.85  thf('37', plain,
% 5.65/5.85      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 5.65/5.85      inference('sup-', [status(thm)], ['35', '36'])).
% 5.65/5.85  thf('38', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('clc', [status(thm)], ['34', '37'])).
% 5.65/5.85  thf('39', plain,
% 5.65/5.85      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.85           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 5.65/5.85      inference('clc', [status(thm)], ['10', '17'])).
% 5.65/5.85  thf('40', plain,
% 5.65/5.85      ((((zip_tseitin_0 @ k1_xboole_0 @ 
% 5.65/5.85          (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 5.65/5.85         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('sup+', [status(thm)], ['38', '39'])).
% 5.65/5.85  thf('41', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | (zip_tseitin_0 @ k1_xboole_0 @ 
% 5.65/5.85            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('simplify', [status(thm)], ['40'])).
% 5.65/5.85  thf('42', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('clc', [status(thm)], ['34', '37'])).
% 5.65/5.85  thf('43', plain,
% 5.65/5.85      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85        | (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 5.65/5.85      inference('sup-', [status(thm)], ['35', '36'])).
% 5.65/5.85  thf('44', plain,
% 5.65/5.85      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 5.65/5.85         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('sup+', [status(thm)], ['42', '43'])).
% 5.65/5.85  thf('45', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('simplify', [status(thm)], ['44'])).
% 5.65/5.85  thf(d3_struct_0, axiom,
% 5.65/5.85    (![A:$i]:
% 5.65/5.85     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.65/5.85  thf('46', plain,
% 5.65/5.85      (![X36 : $i]:
% 5.65/5.85         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 5.65/5.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.65/5.85  thf('47', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.85         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('simplify', [status(thm)], ['44'])).
% 5.65/5.85  thf('48', plain,
% 5.65/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf(d3_tops_1, axiom,
% 5.65/5.85    (![A:$i]:
% 5.65/5.85     ( ( l1_pre_topc @ A ) =>
% 5.65/5.85       ( ![B:$i]:
% 5.65/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85           ( ( v1_tops_1 @ B @ A ) <=>
% 5.65/5.85             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 5.65/5.85  thf('49', plain,
% 5.65/5.85      (![X44 : $i, X45 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 5.65/5.85          | ((k2_pre_topc @ X45 @ X44) != (k2_struct_0 @ X45))
% 5.65/5.85          | (v1_tops_1 @ X44 @ X45)
% 5.65/5.85          | ~ (l1_pre_topc @ X45))),
% 5.65/5.85      inference('cnf', [status(esa)], [d3_tops_1])).
% 5.65/5.85  thf('50', plain,
% 5.65/5.85      ((~ (l1_pre_topc @ sk_A)
% 5.65/5.85        | (v1_tops_1 @ sk_B @ sk_A)
% 5.65/5.85        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 5.65/5.85      inference('sup-', [status(thm)], ['48', '49'])).
% 5.65/5.85  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('52', plain,
% 5.65/5.85      (((v1_tops_1 @ sk_B @ sk_A)
% 5.65/5.85        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 5.65/5.85      inference('demod', [status(thm)], ['50', '51'])).
% 5.65/5.85  thf('53', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 5.65/5.85         | (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 5.65/5.85         | (v1_tops_1 @ sk_B @ sk_A)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('sup-', [status(thm)], ['47', '52'])).
% 5.65/5.85  thf('54', plain,
% 5.65/5.85      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 5.65/5.85         | ~ (l1_struct_0 @ sk_A)
% 5.65/5.85         | (v1_tops_1 @ sk_B @ sk_A)
% 5.65/5.85         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('sup-', [status(thm)], ['46', '53'])).
% 5.65/5.85  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf(dt_l1_pre_topc, axiom,
% 5.65/5.85    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.65/5.85  thf('56', plain,
% 5.65/5.85      (![X37 : $i]: ((l1_struct_0 @ X37) | ~ (l1_pre_topc @ X37))),
% 5.65/5.85      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.65/5.85  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 5.65/5.85      inference('sup-', [status(thm)], ['55', '56'])).
% 5.65/5.85  thf('58', plain,
% 5.65/5.85      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 5.65/5.85         | (v1_tops_1 @ sk_B @ sk_A)
% 5.65/5.85         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('demod', [status(thm)], ['54', '57'])).
% 5.65/5.85  thf('59', plain,
% 5.65/5.85      ((((v3_pre_topc @ k1_xboole_0 @ sk_A) | (v1_tops_1 @ sk_B @ sk_A)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('simplify', [status(thm)], ['58'])).
% 5.65/5.85  thf('60', plain,
% 5.65/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('61', plain,
% 5.65/5.85      (![X44 : $i, X45 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 5.65/5.85          | ~ (v1_tops_1 @ X44 @ X45)
% 5.65/5.85          | ((k2_pre_topc @ X45 @ X44) = (k2_struct_0 @ X45))
% 5.65/5.85          | ~ (l1_pre_topc @ X45))),
% 5.65/5.85      inference('cnf', [status(esa)], [d3_tops_1])).
% 5.65/5.85  thf('62', plain,
% 5.65/5.85      ((~ (l1_pre_topc @ sk_A)
% 5.65/5.85        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 5.65/5.85        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.85      inference('sup-', [status(thm)], ['60', '61'])).
% 5.65/5.85  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.85  thf('64', plain,
% 5.65/5.85      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 5.65/5.85        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.85      inference('demod', [status(thm)], ['62', '63'])).
% 5.65/5.85  thf('65', plain,
% 5.65/5.85      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 5.65/5.85         | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('sup-', [status(thm)], ['59', '64'])).
% 5.65/5.85  thf('66', plain,
% 5.65/5.85      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.85         | (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 5.65/5.85         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('sup+', [status(thm)], ['45', '65'])).
% 5.65/5.85  thf('67', plain,
% 5.65/5.85      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 5.65/5.85         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 5.65/5.85         <= ((![X49 : $i]:
% 5.65/5.85                (((X49) = (k1_xboole_0))
% 5.65/5.85                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.85                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.85                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.85      inference('simplify', [status(thm)], ['66'])).
% 5.65/5.85  thf('68', plain,
% 5.65/5.85      (![X36 : $i]:
% 5.65/5.85         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 5.65/5.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.65/5.85  thf('69', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.85      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.85  thf('70', plain,
% 5.65/5.85      (![X36 : $i]:
% 5.65/5.85         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 5.65/5.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.65/5.85  thf(t29_tops_1, axiom,
% 5.65/5.85    (![A:$i]:
% 5.65/5.85     ( ( l1_pre_topc @ A ) =>
% 5.65/5.85       ( ![B:$i]:
% 5.65/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.85           ( ( v4_pre_topc @ B @ A ) <=>
% 5.65/5.85             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 5.65/5.85  thf('71', plain,
% 5.65/5.85      (![X47 : $i, X48 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 5.65/5.85          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X48) @ X47) @ X48)
% 5.65/5.85          | (v4_pre_topc @ X47 @ X48)
% 5.65/5.85          | ~ (l1_pre_topc @ X48))),
% 5.65/5.85      inference('cnf', [status(esa)], [t29_tops_1])).
% 5.65/5.85  thf('72', plain,
% 5.65/5.85      (![X0 : $i, X1 : $i]:
% 5.65/5.85         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 5.65/5.85          | ~ (l1_struct_0 @ X0)
% 5.65/5.85          | ~ (l1_pre_topc @ X0)
% 5.65/5.85          | (v4_pre_topc @ X1 @ X0)
% 5.65/5.85          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 5.65/5.85      inference('sup-', [status(thm)], ['70', '71'])).
% 5.65/5.85  thf('73', plain,
% 5.65/5.85      (![X0 : $i]:
% 5.65/5.85         (~ (v3_pre_topc @ 
% 5.65/5.85             (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ X0)
% 5.65/5.85          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 5.65/5.85          | ~ (l1_pre_topc @ X0)
% 5.65/5.85          | ~ (l1_struct_0 @ X0))),
% 5.65/5.85      inference('sup-', [status(thm)], ['69', '72'])).
% 5.65/5.85  thf('74', plain,
% 5.65/5.85      (![X0 : $i]:
% 5.65/5.85         (~ (v3_pre_topc @ 
% 5.65/5.85             (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ X0)
% 5.65/5.85          | ~ (l1_struct_0 @ X0)
% 5.65/5.85          | ~ (l1_struct_0 @ X0)
% 5.65/5.85          | ~ (l1_pre_topc @ X0)
% 5.65/5.85          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 5.65/5.85      inference('sup-', [status(thm)], ['68', '73'])).
% 5.65/5.85  thf(t3_boole, axiom,
% 5.65/5.85    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.65/5.85  thf('75', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.65/5.85      inference('cnf', [status(esa)], [t3_boole])).
% 5.65/5.85  thf(t48_xboole_1, axiom,
% 5.65/5.85    (![A:$i,B:$i]:
% 5.65/5.85     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.65/5.85  thf('76', plain,
% 5.65/5.85      (![X7 : $i, X8 : $i]:
% 5.65/5.85         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 5.65/5.85           = (k3_xboole_0 @ X7 @ X8))),
% 5.65/5.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.65/5.85  thf('77', plain,
% 5.65/5.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 5.65/5.85      inference('sup+', [status(thm)], ['75', '76'])).
% 5.65/5.85  thf(t2_boole, axiom,
% 5.65/5.85    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 5.65/5.85  thf('78', plain,
% 5.65/5.85      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 5.65/5.85      inference('cnf', [status(esa)], [t2_boole])).
% 5.65/5.85  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['77', '78'])).
% 5.65/5.86  thf('80', plain,
% 5.65/5.86      (![X7 : $i, X8 : $i]:
% 5.65/5.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 5.65/5.86           = (k3_xboole_0 @ X7 @ X8))),
% 5.65/5.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.65/5.86  thf('81', plain,
% 5.65/5.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['79', '80'])).
% 5.65/5.86  thf('82', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.65/5.86      inference('cnf', [status(esa)], [t3_boole])).
% 5.65/5.86  thf('83', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('demod', [status(thm)], ['81', '82'])).
% 5.65/5.86  thf(t100_xboole_1, axiom,
% 5.65/5.86    (![A:$i,B:$i]:
% 5.65/5.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.65/5.86  thf('84', plain,
% 5.65/5.86      (![X3 : $i, X4 : $i]:
% 5.65/5.86         ((k4_xboole_0 @ X3 @ X4)
% 5.65/5.86           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 5.65/5.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.65/5.86  thf('85', plain,
% 5.65/5.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['83', '84'])).
% 5.65/5.86  thf('86', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.86      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.86  thf(d5_subset_1, axiom,
% 5.65/5.86    (![A:$i,B:$i]:
% 5.65/5.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.65/5.86       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.65/5.86  thf('87', plain,
% 5.65/5.86      (![X11 : $i, X12 : $i]:
% 5.65/5.86         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 5.65/5.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 5.65/5.86      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.65/5.86  thf('88', plain,
% 5.65/5.86      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['86', '87'])).
% 5.65/5.86  thf('89', plain,
% 5.65/5.86      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['85', '88'])).
% 5.65/5.86  thf('90', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['77', '78'])).
% 5.65/5.86  thf('91', plain,
% 5.65/5.86      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['86', '87'])).
% 5.65/5.86  thf('92', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['90', '91'])).
% 5.65/5.86  thf('93', plain,
% 5.65/5.86      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['85', '88'])).
% 5.65/5.86  thf('94', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['92', '93'])).
% 5.65/5.86  thf('95', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 5.65/5.86          | ~ (l1_struct_0 @ X0)
% 5.65/5.86          | ~ (l1_struct_0 @ X0)
% 5.65/5.86          | ~ (l1_pre_topc @ X0)
% 5.65/5.86          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 5.65/5.86      inference('demod', [status(thm)], ['74', '89', '94'])).
% 5.65/5.86  thf('96', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         ((v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 5.65/5.86          | ~ (l1_pre_topc @ X0)
% 5.65/5.86          | ~ (l1_struct_0 @ X0)
% 5.65/5.86          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 5.65/5.86      inference('simplify', [status(thm)], ['95'])).
% 5.65/5.86  thf('97', plain,
% 5.65/5.86      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | ~ (l1_struct_0 @ sk_A)
% 5.65/5.86         | ~ (l1_pre_topc @ sk_A)
% 5.65/5.86         | (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['67', '96'])).
% 5.65/5.86  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 5.65/5.86      inference('sup-', [status(thm)], ['55', '56'])).
% 5.65/5.86  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('100', plain,
% 5.65/5.86      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('demod', [status(thm)], ['97', '98', '99'])).
% 5.65/5.86  thf('101', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.86      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.86  thf('102', plain,
% 5.65/5.86      (![X36 : $i]:
% 5.65/5.86         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 5.65/5.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.65/5.86  thf(t52_pre_topc, axiom,
% 5.65/5.86    (![A:$i]:
% 5.65/5.86     ( ( l1_pre_topc @ A ) =>
% 5.65/5.86       ( ![B:$i]:
% 5.65/5.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.86           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 5.65/5.86             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 5.65/5.86               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 5.65/5.86  thf('103', plain,
% 5.65/5.86      (![X38 : $i, X39 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 5.65/5.86          | ~ (v4_pre_topc @ X38 @ X39)
% 5.65/5.86          | ((k2_pre_topc @ X39 @ X38) = (X38))
% 5.65/5.86          | ~ (l1_pre_topc @ X39))),
% 5.65/5.86      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.65/5.86  thf('104', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 5.65/5.86          | ~ (l1_struct_0 @ X0)
% 5.65/5.86          | ~ (l1_pre_topc @ X0)
% 5.65/5.86          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 5.65/5.86          | ~ (v4_pre_topc @ X1 @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['102', '103'])).
% 5.65/5.86  thf('105', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 5.65/5.86          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 5.65/5.86          | ~ (l1_pre_topc @ X0)
% 5.65/5.86          | ~ (l1_struct_0 @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['101', '104'])).
% 5.65/5.86  thf('106', plain,
% 5.65/5.86      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | ~ (l1_struct_0 @ sk_A)
% 5.65/5.86         | ~ (l1_pre_topc @ sk_A)
% 5.65/5.86         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['100', '105'])).
% 5.65/5.86  thf('107', plain, ((l1_struct_0 @ sk_A)),
% 5.65/5.86      inference('sup-', [status(thm)], ['55', '56'])).
% 5.65/5.86  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('109', plain,
% 5.65/5.86      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('demod', [status(thm)], ['106', '107', '108'])).
% 5.65/5.86  thf('110', plain,
% 5.65/5.86      (![X36 : $i]:
% 5.65/5.86         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 5.65/5.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.65/5.86  thf('111', plain,
% 5.65/5.86      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 5.65/5.86         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('simplify', [status(thm)], ['66'])).
% 5.65/5.86  thf('112', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.86      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.86  thf('113', plain,
% 5.65/5.86      (![X47 : $i, X48 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 5.65/5.86          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X48) @ X47) @ X48)
% 5.65/5.86          | (v4_pre_topc @ X47 @ X48)
% 5.65/5.86          | ~ (l1_pre_topc @ X48))),
% 5.65/5.86      inference('cnf', [status(esa)], [t29_tops_1])).
% 5.65/5.86  thf('114', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.65/5.86          | ~ (v3_pre_topc @ 
% 5.65/5.86               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['112', '113'])).
% 5.65/5.86  thf('115', plain,
% 5.65/5.86      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['85', '88'])).
% 5.65/5.86  thf('116', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['92', '93'])).
% 5.65/5.86  thf('117', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.65/5.86          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 5.65/5.86      inference('demod', [status(thm)], ['114', '115', '116'])).
% 5.65/5.86  thf('118', plain,
% 5.65/5.86      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 5.65/5.86         | ~ (l1_pre_topc @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['111', '117'])).
% 5.65/5.86  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('120', plain,
% 5.65/5.86      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('demod', [status(thm)], ['118', '119'])).
% 5.65/5.86  thf('121', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.86      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.86  thf('122', plain,
% 5.65/5.86      (![X38 : $i, X39 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 5.65/5.86          | ~ (v4_pre_topc @ X38 @ X39)
% 5.65/5.86          | ((k2_pre_topc @ X39 @ X38) = (X38))
% 5.65/5.86          | ~ (l1_pre_topc @ X39))),
% 5.65/5.86      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.65/5.86  thf('123', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 5.65/5.86          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['121', '122'])).
% 5.65/5.86  thf('124', plain,
% 5.65/5.86      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 5.65/5.86         | ~ (l1_pre_topc @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['120', '123'])).
% 5.65/5.86  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('126', plain,
% 5.65/5.86      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('demod', [status(thm)], ['124', '125'])).
% 5.65/5.86  thf('127', plain,
% 5.65/5.86      (((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 5.65/5.86         | ~ (l1_struct_0 @ sk_A)
% 5.65/5.86         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('sup+', [status(thm)], ['110', '126'])).
% 5.65/5.86  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 5.65/5.86      inference('sup-', [status(thm)], ['55', '56'])).
% 5.65/5.86  thf('129', plain,
% 5.65/5.86      (((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 5.65/5.86         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('demod', [status(thm)], ['127', '128'])).
% 5.65/5.86  thf('130', plain,
% 5.65/5.86      (((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 5.65/5.86         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 5.65/5.86         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('sup+', [status(thm)], ['109', '129'])).
% 5.65/5.86  thf('131', plain,
% 5.65/5.86      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('simplify', [status(thm)], ['130'])).
% 5.65/5.86  thf('132', plain,
% 5.65/5.86      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('simplify', [status(thm)], ['130'])).
% 5.65/5.86  thf('133', plain,
% 5.65/5.86      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.86         | (zip_tseitin_0 @ k1_xboole_0 @ 
% 5.65/5.86            (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('demod', [status(thm)], ['41', '131', '132'])).
% 5.65/5.86  thf('134', plain,
% 5.65/5.86      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.65/5.86         ((r2_hidden @ X27 @ X25) | ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X26))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.65/5.86  thf('135', plain,
% 5.65/5.86      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.86         | (r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 5.65/5.86            k1_xboole_0)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['133', '134'])).
% 5.65/5.86  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('137', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['92', '93'])).
% 5.65/5.86  thf(fc10_tops_1, axiom,
% 5.65/5.86    (![A:$i]:
% 5.65/5.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.65/5.86       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 5.65/5.86  thf('138', plain,
% 5.65/5.86      (![X46 : $i]:
% 5.65/5.86         ((v3_pre_topc @ (k2_struct_0 @ X46) @ X46)
% 5.65/5.86          | ~ (l1_pre_topc @ X46)
% 5.65/5.86          | ~ (v2_pre_topc @ X46))),
% 5.65/5.86      inference('cnf', [status(esa)], [fc10_tops_1])).
% 5.65/5.86  thf('139', plain,
% 5.65/5.86      (![X36 : $i]:
% 5.65/5.86         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 5.65/5.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.65/5.86  thf(t4_subset_1, axiom,
% 5.65/5.86    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.65/5.86  thf('140', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf('141', plain,
% 5.65/5.86      (![X47 : $i, X48 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 5.65/5.86          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X48) @ X47) @ X48)
% 5.65/5.86          | (v4_pre_topc @ X47 @ X48)
% 5.65/5.86          | ~ (l1_pre_topc @ X48))),
% 5.65/5.86      inference('cnf', [status(esa)], [t29_tops_1])).
% 5.65/5.86  thf('142', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 5.65/5.86          | ~ (v3_pre_topc @ 
% 5.65/5.86               (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['140', '141'])).
% 5.65/5.86  thf('143', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf('144', plain,
% 5.65/5.86      (![X11 : $i, X12 : $i]:
% 5.65/5.86         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 5.65/5.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 5.65/5.86      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.65/5.86  thf('145', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['143', '144'])).
% 5.65/5.86  thf('146', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.65/5.86      inference('cnf', [status(esa)], [t3_boole])).
% 5.65/5.86  thf('147', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['145', '146'])).
% 5.65/5.86  thf('148', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 5.65/5.86          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 5.65/5.86      inference('demod', [status(thm)], ['142', '147'])).
% 5.65/5.86  thf('149', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 5.65/5.86          | ~ (l1_struct_0 @ X0)
% 5.65/5.86          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 5.65/5.86          | ~ (l1_pre_topc @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['139', '148'])).
% 5.65/5.86  thf('150', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (v2_pre_topc @ X0)
% 5.65/5.86          | ~ (l1_pre_topc @ X0)
% 5.65/5.86          | ~ (l1_pre_topc @ X0)
% 5.65/5.86          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 5.65/5.86          | ~ (l1_struct_0 @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['138', '149'])).
% 5.65/5.86  thf('151', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (l1_struct_0 @ X0)
% 5.65/5.86          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 5.65/5.86          | ~ (l1_pre_topc @ X0)
% 5.65/5.86          | ~ (v2_pre_topc @ X0))),
% 5.65/5.86      inference('simplify', [status(thm)], ['150'])).
% 5.65/5.86  thf('152', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         ((v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 5.65/5.86          | ~ (v2_pre_topc @ X1)
% 5.65/5.86          | ~ (l1_pre_topc @ X1)
% 5.65/5.86          | ~ (l1_struct_0 @ X1))),
% 5.65/5.86      inference('sup+', [status(thm)], ['137', '151'])).
% 5.65/5.86  thf('153', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (l1_struct_0 @ sk_A)
% 5.65/5.86          | ~ (v2_pre_topc @ sk_A)
% 5.65/5.86          | (v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ sk_A))),
% 5.65/5.86      inference('sup-', [status(thm)], ['136', '152'])).
% 5.65/5.86  thf('154', plain, ((l1_struct_0 @ sk_A)),
% 5.65/5.86      inference('sup-', [status(thm)], ['55', '56'])).
% 5.65/5.86  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('156', plain,
% 5.65/5.86      (![X0 : $i]: (v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ sk_A)),
% 5.65/5.86      inference('demod', [status(thm)], ['153', '154', '155'])).
% 5.65/5.86  thf('157', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['92', '93'])).
% 5.65/5.86  thf('158', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf('159', plain,
% 5.65/5.86      (![X38 : $i, X39 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 5.65/5.86          | ~ (v4_pre_topc @ X38 @ X39)
% 5.65/5.86          | ((k2_pre_topc @ X39 @ X38) = (X38))
% 5.65/5.86          | ~ (l1_pre_topc @ X39))),
% 5.65/5.86      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.65/5.86  thf('160', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 5.65/5.86          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['158', '159'])).
% 5.65/5.86  thf('161', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (~ (v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 5.65/5.86          | ((k2_pre_topc @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 5.65/5.86          | ~ (l1_pre_topc @ X1))),
% 5.65/5.86      inference('sup-', [status(thm)], ['157', '160'])).
% 5.65/5.86  thf('162', plain,
% 5.65/5.86      ((~ (l1_pre_topc @ sk_A)
% 5.65/5.86        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['156', '161'])).
% 5.65/5.86  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('164', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['162', '163'])).
% 5.65/5.86  thf('165', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.86      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.86  thf('166', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf(t54_pre_topc, axiom,
% 5.65/5.86    (![A:$i]:
% 5.65/5.86     ( ( l1_pre_topc @ A ) =>
% 5.65/5.86       ( ![B:$i]:
% 5.65/5.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.86           ( ![C:$i]:
% 5.65/5.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.65/5.86               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 5.65/5.86                 ( ( ~( v2_struct_0 @ A ) ) & 
% 5.65/5.86                   ( ![D:$i]:
% 5.65/5.86                     ( ( m1_subset_1 @
% 5.65/5.86                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.65/5.86                       ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 5.65/5.86                            ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.65/5.86  thf('167', plain,
% 5.65/5.86      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 5.65/5.86          | ~ (r2_hidden @ X42 @ (k2_pre_topc @ X41 @ X40))
% 5.65/5.86          | ~ (r1_xboole_0 @ X40 @ X43)
% 5.65/5.86          | ~ (r2_hidden @ X42 @ X43)
% 5.65/5.86          | ~ (v3_pre_topc @ X43 @ X41)
% 5.65/5.86          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 5.65/5.86          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 5.65/5.86          | ~ (l1_pre_topc @ X41))),
% 5.65/5.86      inference('cnf', [status(esa)], [t54_pre_topc])).
% 5.65/5.86  thf('168', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.65/5.86          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.65/5.86          | ~ (v3_pre_topc @ X2 @ X0)
% 5.65/5.86          | ~ (r2_hidden @ X1 @ X2)
% 5.65/5.86          | ~ (r1_xboole_0 @ k1_xboole_0 @ X2)
% 5.65/5.86          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['166', '167'])).
% 5.65/5.86  thf('169', plain,
% 5.65/5.86      (![X7 : $i, X8 : $i]:
% 5.65/5.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 5.65/5.86           = (k3_xboole_0 @ X7 @ X8))),
% 5.65/5.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.65/5.86  thf(t4_boole, axiom,
% 5.65/5.86    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 5.65/5.86  thf('170', plain,
% 5.65/5.86      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_boole])).
% 5.65/5.86  thf('171', plain,
% 5.65/5.86      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['169', '170'])).
% 5.65/5.86  thf(d7_xboole_0, axiom,
% 5.65/5.86    (![A:$i,B:$i]:
% 5.65/5.86     ( ( r1_xboole_0 @ A @ B ) <=>
% 5.65/5.86       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 5.65/5.86  thf('172', plain,
% 5.65/5.86      (![X0 : $i, X2 : $i]:
% 5.65/5.86         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 5.65/5.86      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.65/5.86  thf('173', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['171', '172'])).
% 5.65/5.86  thf('174', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.65/5.86      inference('simplify', [status(thm)], ['173'])).
% 5.65/5.86  thf('175', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.65/5.86          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.65/5.86          | ~ (v3_pre_topc @ X2 @ X0)
% 5.65/5.86          | ~ (r2_hidden @ X1 @ X2)
% 5.65/5.86          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 5.65/5.86      inference('demod', [status(thm)], ['168', '174'])).
% 5.65/5.86  thf('176', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0))
% 5.65/5.86          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 5.65/5.86          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.65/5.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.65/5.86          | ~ (l1_pre_topc @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['165', '175'])).
% 5.65/5.86  thf('177', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.65/5.86          | ~ (l1_pre_topc @ sk_A)
% 5.65/5.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.65/5.86          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 5.65/5.86          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['164', '176'])).
% 5.65/5.86  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('179', plain,
% 5.65/5.86      (![X0 : $i]: (v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ sk_A)),
% 5.65/5.86      inference('demod', [status(thm)], ['153', '154', '155'])).
% 5.65/5.86  thf('180', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['77', '78'])).
% 5.65/5.86  thf('181', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf('182', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 5.65/5.86      inference('sup+', [status(thm)], ['180', '181'])).
% 5.65/5.86  thf('183', plain,
% 5.65/5.86      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['86', '87'])).
% 5.65/5.86  thf('184', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 5.65/5.86      inference('demod', [status(thm)], ['182', '183'])).
% 5.65/5.86  thf('185', plain,
% 5.65/5.86      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['85', '88'])).
% 5.65/5.86  thf('186', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (m1_subset_1 @ (k5_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 5.65/5.86      inference('demod', [status(thm)], ['184', '185'])).
% 5.65/5.86  thf('187', plain,
% 5.65/5.86      (![X47 : $i, X48 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 5.65/5.86          | ~ (v4_pre_topc @ X47 @ X48)
% 5.65/5.86          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X48) @ X47) @ X48)
% 5.65/5.86          | ~ (l1_pre_topc @ X48))),
% 5.65/5.86      inference('cnf', [status(esa)], [t29_tops_1])).
% 5.65/5.86  thf('188', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | (v3_pre_topc @ 
% 5.65/5.86             (k3_subset_1 @ (u1_struct_0 @ X0) @ (k5_xboole_0 @ X1 @ X1)) @ X0)
% 5.65/5.86          | ~ (v4_pre_topc @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['186', '187'])).
% 5.65/5.86  thf('189', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['92', '93'])).
% 5.65/5.86  thf('190', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 5.65/5.86      inference('sup+', [status(thm)], ['145', '146'])).
% 5.65/5.86  thf('191', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         ((k3_subset_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 5.65/5.86      inference('sup+', [status(thm)], ['189', '190'])).
% 5.65/5.86  thf('192', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.65/5.86          | ~ (v4_pre_topc @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 5.65/5.86      inference('demod', [status(thm)], ['188', '191'])).
% 5.65/5.86  thf('193', plain,
% 5.65/5.86      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 5.65/5.86      inference('sup-', [status(thm)], ['179', '192'])).
% 5.65/5.86  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('195', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 5.65/5.86      inference('demod', [status(thm)], ['193', '194'])).
% 5.65/5.86  thf('196', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.65/5.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.65/5.86          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.86      inference('demod', [status(thm)], ['177', '178', '195'])).
% 5.65/5.86  thf('197', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf(t4_subset, axiom,
% 5.65/5.86    (![A:$i,B:$i,C:$i]:
% 5.65/5.86     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 5.65/5.86       ( m1_subset_1 @ A @ C ) ))).
% 5.65/5.86  thf('198', plain,
% 5.65/5.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.65/5.86         (~ (r2_hidden @ X22 @ X23)
% 5.65/5.86          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 5.65/5.86          | (m1_subset_1 @ X22 @ X24))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset])).
% 5.65/5.86  thf('199', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['197', '198'])).
% 5.65/5.86  thf('200', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.65/5.86          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 5.65/5.86      inference('clc', [status(thm)], ['196', '199'])).
% 5.65/5.86  thf('201', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf(l3_subset_1, axiom,
% 5.65/5.86    (![A:$i,B:$i]:
% 5.65/5.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.65/5.86       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 5.65/5.86  thf('202', plain,
% 5.65/5.86      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.65/5.86         (~ (r2_hidden @ X16 @ X17)
% 5.65/5.86          | (r2_hidden @ X16 @ X18)
% 5.65/5.86          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 5.65/5.86      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.65/5.86  thf('203', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['201', '202'])).
% 5.65/5.86  thf('204', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.65/5.86      inference('clc', [status(thm)], ['200', '203'])).
% 5.65/5.86  thf('205', plain,
% 5.65/5.86      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('clc', [status(thm)], ['135', '204'])).
% 5.65/5.86  thf('206', plain,
% 5.65/5.86      (((v1_tops_1 @ sk_B @ sk_A)
% 5.65/5.86        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 5.65/5.86      inference('demod', [status(thm)], ['50', '51'])).
% 5.65/5.86  thf('207', plain,
% 5.65/5.86      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 5.65/5.86         | (v1_tops_1 @ sk_B @ sk_A)))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['205', '206'])).
% 5.65/5.86  thf('208', plain,
% 5.65/5.86      (((v1_tops_1 @ sk_B @ sk_A))
% 5.65/5.86         <= ((![X49 : $i]:
% 5.65/5.86                (((X49) = (k1_xboole_0))
% 5.65/5.86                 | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86                 | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86                 | ~ (r1_xboole_0 @ sk_B @ X49))))),
% 5.65/5.86      inference('simplify', [status(thm)], ['207'])).
% 5.65/5.86  thf('209', plain,
% 5.65/5.86      (((r1_xboole_0 @ sk_B @ sk_C) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('210', plain,
% 5.65/5.86      ((~ (v1_tops_1 @ sk_B @ sk_A)) <= (~ ((v1_tops_1 @ sk_B @ sk_A)))),
% 5.65/5.86      inference('split', [status(esa)], ['209'])).
% 5.65/5.86  thf('211', plain,
% 5.65/5.86      (~
% 5.65/5.86       (![X49 : $i]:
% 5.65/5.86          (((X49) = (k1_xboole_0))
% 5.65/5.86           | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86           | ~ (v3_pre_topc @ X49 @ sk_A)
% 5.65/5.86           | ~ (r1_xboole_0 @ sk_B @ X49))) | 
% 5.65/5.86       ((v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('sup-', [status(thm)], ['208', '210'])).
% 5.65/5.86  thf('212', plain,
% 5.65/5.86      (((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('split', [status(esa)], ['209'])).
% 5.65/5.86  thf('213', plain,
% 5.65/5.86      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('214', plain,
% 5.65/5.86      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('split', [status(esa)], ['213'])).
% 5.65/5.86  thf('215', plain,
% 5.65/5.86      ((((sk_C) != (k1_xboole_0)) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('216', plain,
% 5.65/5.86      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('split', [status(esa)], ['215'])).
% 5.65/5.86  thf('217', plain,
% 5.65/5.86      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('218', plain,
% 5.65/5.86      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 5.65/5.86       ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('split', [status(esa)], ['217'])).
% 5.65/5.86  thf('219', plain,
% 5.65/5.86      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('split', [status(esa)], ['217'])).
% 5.65/5.86  thf('220', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf('221', plain,
% 5.65/5.86      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | (r2_hidden @ (sk_D @ X32 @ X30 @ X31) @ (u1_struct_0 @ X31))
% 5.65/5.86          | ((X32) = (k2_pre_topc @ X31 @ X30))
% 5.65/5.86          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | ~ (l1_pre_topc @ X31))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.65/5.86  thf('222', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.65/5.86          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 5.65/5.86          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['220', '221'])).
% 5.65/5.86  thf('223', plain,
% 5.65/5.86      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.65/5.86         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 5.65/5.86         | ~ (l1_pre_topc @ sk_A)))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['219', '222'])).
% 5.65/5.86  thf('224', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['162', '163'])).
% 5.65/5.86  thf('225', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('226', plain,
% 5.65/5.86      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.65/5.86         | ((sk_C) = (k1_xboole_0))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('demod', [status(thm)], ['223', '224', '225'])).
% 5.65/5.86  thf('227', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 5.65/5.86      inference('demod', [status(thm)], ['193', '194'])).
% 5.65/5.86  thf('228', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.65/5.86      inference('simplify', [status(thm)], ['173'])).
% 5.65/5.86  thf('229', plain,
% 5.65/5.86      (![X25 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 5.65/5.86         ((zip_tseitin_0 @ X25 @ X27 @ X28 @ X29)
% 5.65/5.86          | ~ (r1_xboole_0 @ X28 @ X25)
% 5.65/5.86          | ~ (r2_hidden @ X27 @ X25)
% 5.65/5.86          | ~ (v3_pre_topc @ X25 @ X29))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.65/5.86  thf('230', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.65/5.86         (~ (v3_pre_topc @ X0 @ X1)
% 5.65/5.86          | ~ (r2_hidden @ X2 @ X0)
% 5.65/5.86          | (zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1))),
% 5.65/5.86      inference('sup-', [status(thm)], ['228', '229'])).
% 5.65/5.86  thf('231', plain,
% 5.65/5.86      (![X0 : $i]:
% 5.65/5.86         ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0 @ sk_A)
% 5.65/5.86          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['227', '230'])).
% 5.65/5.86  thf('232', plain,
% 5.65/5.86      (((((sk_C) = (k1_xboole_0))
% 5.65/5.86         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 5.65/5.86            (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['226', '231'])).
% 5.65/5.86  thf('233', plain,
% 5.65/5.86      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 5.65/5.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.65/5.86  thf('234', plain,
% 5.65/5.86      (![X30 : $i, X31 : $i, X32 : $i, X35 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | (r2_hidden @ (sk_D @ X32 @ X30 @ X31) @ X32)
% 5.65/5.86          | ~ (zip_tseitin_0 @ X35 @ (sk_D @ X32 @ X30 @ X31) @ X30 @ X31)
% 5.65/5.86          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | ((X32) = (k2_pre_topc @ X31 @ X30))
% 5.65/5.86          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | ~ (l1_pre_topc @ X31))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.65/5.86  thf('235', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X0)
% 5.65/5.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.65/5.86          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 5.65/5.86          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.65/5.86          | ~ (zip_tseitin_0 @ X2 @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 5.65/5.86               k1_xboole_0 @ X0)
% 5.65/5.86          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 5.65/5.86      inference('sup-', [status(thm)], ['233', '234'])).
% 5.65/5.86  thf('236', plain,
% 5.65/5.86      (((((sk_C) = (k1_xboole_0))
% 5.65/5.86         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 5.65/5.86         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.65/5.86              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 5.65/5.86         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86         | ~ (l1_pre_topc @ sk_A)))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['232', '235'])).
% 5.65/5.86  thf('237', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.86      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.86  thf('238', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 5.65/5.86      inference('demod', [status(thm)], ['162', '163'])).
% 5.65/5.86  thf('239', plain,
% 5.65/5.86      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('split', [status(esa)], ['217'])).
% 5.65/5.86  thf('240', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('241', plain,
% 5.65/5.86      (((((sk_C) = (k1_xboole_0))
% 5.65/5.86         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 5.65/5.86         | ((sk_C) = (k1_xboole_0))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('demod', [status(thm)], ['236', '237', '238', '239', '240'])).
% 5.65/5.86  thf('242', plain,
% 5.65/5.86      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 5.65/5.86         | ((sk_C) = (k1_xboole_0))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('simplify', [status(thm)], ['241'])).
% 5.65/5.86  thf('243', plain,
% 5.65/5.86      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 5.65/5.86      inference('split', [status(esa)], ['213'])).
% 5.65/5.86  thf('244', plain,
% 5.65/5.86      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 5.65/5.86      inference('split', [status(esa)], ['209'])).
% 5.65/5.86  thf('245', plain,
% 5.65/5.86      (![X25 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 5.65/5.86         ((zip_tseitin_0 @ X25 @ X27 @ X28 @ X29)
% 5.65/5.86          | ~ (r1_xboole_0 @ X28 @ X25)
% 5.65/5.86          | ~ (r2_hidden @ X27 @ X25)
% 5.65/5.86          | ~ (v3_pre_topc @ X25 @ X29))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.65/5.86  thf('246', plain,
% 5.65/5.86      ((![X0 : $i, X1 : $i]:
% 5.65/5.86          (~ (v3_pre_topc @ sk_C @ X0)
% 5.65/5.86           | ~ (r2_hidden @ X1 @ sk_C)
% 5.65/5.86           | (zip_tseitin_0 @ sk_C @ X1 @ sk_B @ X0)))
% 5.65/5.86         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['244', '245'])).
% 5.65/5.86  thf('247', plain,
% 5.65/5.86      ((![X0 : $i]:
% 5.65/5.86          ((zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A)
% 5.65/5.86           | ~ (r2_hidden @ X0 @ sk_C)))
% 5.65/5.86         <= (((r1_xboole_0 @ sk_B @ sk_C)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['243', '246'])).
% 5.65/5.86  thf('248', plain,
% 5.65/5.86      (((((sk_C) = (k1_xboole_0))
% 5.65/5.86         | (zip_tseitin_0 @ sk_C @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_B @ 
% 5.65/5.86            sk_A)))
% 5.65/5.86         <= (((r1_xboole_0 @ sk_B @ sk_C)) & 
% 5.65/5.86             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 5.65/5.86             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['242', '247'])).
% 5.65/5.86  thf('249', plain,
% 5.65/5.86      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('split', [status(esa)], ['217'])).
% 5.65/5.86  thf('250', plain,
% 5.65/5.86      (((v1_tops_1 @ sk_B @ sk_A)) <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 5.65/5.86      inference('split', [status(esa)], ['0'])).
% 5.65/5.86  thf('251', plain,
% 5.65/5.86      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 5.65/5.86        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 5.65/5.86      inference('demod', [status(thm)], ['62', '63'])).
% 5.65/5.86  thf('252', plain,
% 5.65/5.86      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 5.65/5.86         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['250', '251'])).
% 5.65/5.86  thf('253', plain,
% 5.65/5.86      (![X36 : $i]:
% 5.65/5.86         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 5.65/5.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.65/5.86  thf('254', plain,
% 5.65/5.86      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | ((X32) != (k2_pre_topc @ X31 @ X30))
% 5.65/5.86          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | ~ (zip_tseitin_0 @ X33 @ X34 @ X30 @ X31)
% 5.65/5.86          | ~ (r2_hidden @ X34 @ X32)
% 5.65/5.86          | ~ (r2_hidden @ X34 @ (u1_struct_0 @ X31))
% 5.65/5.86          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | ~ (l1_pre_topc @ X31))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.65/5.86  thf('255', plain,
% 5.65/5.86      (![X30 : $i, X31 : $i, X33 : $i, X34 : $i]:
% 5.65/5.86         (~ (l1_pre_topc @ X31)
% 5.65/5.86          | ~ (m1_subset_1 @ (k2_pre_topc @ X31 @ X30) @ 
% 5.65/5.86               (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | ~ (r2_hidden @ X34 @ (u1_struct_0 @ X31))
% 5.65/5.86          | ~ (r2_hidden @ X34 @ (k2_pre_topc @ X31 @ X30))
% 5.65/5.86          | ~ (zip_tseitin_0 @ X33 @ X34 @ X30 @ X31)
% 5.65/5.86          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.65/5.86          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 5.65/5.86      inference('simplify', [status(thm)], ['254'])).
% 5.65/5.86  thf('256', plain,
% 5.65/5.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.65/5.86         (~ (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 5.65/5.86             (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 5.65/5.86          | ~ (l1_struct_0 @ X0)
% 5.65/5.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.65/5.86          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.65/5.86          | ~ (zip_tseitin_0 @ X2 @ X3 @ X1 @ X0)
% 5.65/5.86          | ~ (r2_hidden @ X3 @ (k2_pre_topc @ X0 @ X1))
% 5.65/5.86          | ~ (r2_hidden @ X3 @ (u1_struct_0 @ X0))
% 5.65/5.86          | ~ (l1_pre_topc @ X0))),
% 5.65/5.86      inference('sup-', [status(thm)], ['253', '255'])).
% 5.65/5.86  thf('257', plain,
% 5.65/5.86      ((![X0 : $i, X1 : $i]:
% 5.65/5.86          (~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 5.65/5.86              (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.65/5.86           | ~ (l1_pre_topc @ sk_A)
% 5.65/5.86           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.65/5.86           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 5.65/5.86           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 5.65/5.86           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.65/5.86           | ~ (l1_struct_0 @ sk_A)))
% 5.65/5.86         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['252', '256'])).
% 5.65/5.86  thf('258', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 5.65/5.86      inference('demod', [status(thm)], ['2', '3'])).
% 5.65/5.86  thf('259', plain, ((l1_pre_topc @ sk_A)),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('260', plain,
% 5.65/5.86      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 5.65/5.86         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 5.65/5.86      inference('sup-', [status(thm)], ['250', '251'])).
% 5.65/5.86  thf('261', plain,
% 5.65/5.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.65/5.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.65/5.86  thf('262', plain, ((l1_struct_0 @ sk_A)),
% 5.65/5.86      inference('sup-', [status(thm)], ['55', '56'])).
% 5.65/5.86  thf('263', plain,
% 5.65/5.86      ((![X0 : $i, X1 : $i]:
% 5.65/5.86          (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.65/5.86           | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 5.65/5.86           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 5.65/5.86           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 5.65/5.86         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 5.65/5.86      inference('demod', [status(thm)],
% 5.65/5.86                ['257', '258', '259', '260', '261', '262'])).
% 5.65/5.86  thf('264', plain,
% 5.65/5.86      ((![X0 : $i]:
% 5.65/5.86          (~ (zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A)
% 5.65/5.86           | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 5.65/5.86           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))))
% 5.65/5.86         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 5.65/5.86             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['249', '263'])).
% 5.65/5.86  thf('265', plain,
% 5.65/5.86      (((((sk_C) = (k1_xboole_0))
% 5.65/5.86         | ~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 5.65/5.86              (u1_struct_0 @ sk_A))
% 5.65/5.86         | ~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 5.65/5.86              (k2_struct_0 @ sk_A))))
% 5.65/5.86         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 5.65/5.86             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 5.65/5.86             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 5.65/5.86             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['248', '264'])).
% 5.65/5.86  thf('266', plain,
% 5.65/5.86      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.65/5.86         | ((sk_C) = (k1_xboole_0))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('demod', [status(thm)], ['223', '224', '225'])).
% 5.65/5.86  thf('267', plain,
% 5.65/5.86      (((~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 5.65/5.86            (k2_struct_0 @ sk_A))
% 5.65/5.86         | ((sk_C) = (k1_xboole_0))))
% 5.65/5.86         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 5.65/5.86             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 5.65/5.86             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 5.65/5.86             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('clc', [status(thm)], ['265', '266'])).
% 5.65/5.86  thf('268', plain,
% 5.65/5.86      (![X36 : $i]:
% 5.65/5.86         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 5.65/5.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.65/5.86  thf('269', plain,
% 5.65/5.86      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 5.65/5.86         | ((sk_C) = (k1_xboole_0))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('demod', [status(thm)], ['223', '224', '225'])).
% 5.65/5.86  thf('270', plain,
% 5.65/5.86      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 5.65/5.86         | ~ (l1_struct_0 @ sk_A)
% 5.65/5.86         | ((sk_C) = (k1_xboole_0))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('sup+', [status(thm)], ['268', '269'])).
% 5.65/5.86  thf('271', plain, ((l1_struct_0 @ sk_A)),
% 5.65/5.86      inference('sup-', [status(thm)], ['55', '56'])).
% 5.65/5.86  thf('272', plain,
% 5.65/5.86      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 5.65/5.86         | ((sk_C) = (k1_xboole_0))))
% 5.65/5.86         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('demod', [status(thm)], ['270', '271'])).
% 5.65/5.86  thf('273', plain,
% 5.65/5.86      ((((sk_C) = (k1_xboole_0)))
% 5.65/5.86         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 5.65/5.86             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 5.65/5.86             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 5.65/5.86             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('clc', [status(thm)], ['267', '272'])).
% 5.65/5.86  thf('274', plain,
% 5.65/5.86      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 5.65/5.86      inference('split', [status(esa)], ['215'])).
% 5.65/5.86  thf('275', plain,
% 5.65/5.86      ((((sk_C) != (sk_C)))
% 5.65/5.86         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 5.65/5.86             ((v1_tops_1 @ sk_B @ sk_A)) & 
% 5.65/5.86             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 5.65/5.86             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 5.65/5.86             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.65/5.86      inference('sup-', [status(thm)], ['273', '274'])).
% 5.65/5.86  thf('276', plain,
% 5.65/5.86      (~ ((v1_tops_1 @ sk_B @ sk_A)) | 
% 5.65/5.86       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 5.65/5.86       ~ ((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 5.65/5.86       (((sk_C) = (k1_xboole_0)))),
% 5.65/5.86      inference('simplify', [status(thm)], ['275'])).
% 5.65/5.86  thf('277', plain, ($false),
% 5.65/5.86      inference('sat_resolution*', [status(thm)],
% 5.65/5.86                ['1', '211', '212', '214', '216', '218', '276'])).
% 5.65/5.86  
% 5.65/5.86  % SZS output end Refutation
% 5.65/5.86  
% 5.70/5.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
