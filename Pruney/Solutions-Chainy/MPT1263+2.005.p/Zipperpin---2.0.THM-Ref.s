%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pa7CJ6N6UI

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:06 EST 2020

% Result     : Theorem 54.39s
% Output     : Refutation 54.39s
% Verified   : 
% Statistics : Number of formulae       :  391 (4975 expanded)
%              Number of leaves         :   46 (1506 expanded)
%              Depth                    :   36
%              Number of atoms          : 4582 (64673 expanded)
%              Number of equality atoms :  243 (3007 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

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

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X50: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X50 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_B @ X50 )
      | ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X14 ) @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X33 @ X31 @ X32 ) @ X33 )
      | ( zip_tseitin_0 @ ( sk_E @ X33 @ X31 @ X32 ) @ ( sk_D @ X33 @ X31 @ X32 ) @ X31 @ X32 )
      | ( X33
        = ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r2_hidden @ ( sk_D @ X33 @ X31 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ( X33
        = ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ X29 @ X26 )
      | ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X27 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X33 @ X31 @ X32 ) @ X33 )
      | ( m1_subset_1 @ ( sk_E @ X33 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( X33
        = ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
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
    ( ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,
    ( ( ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','17'])).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v3_pre_topc @ X26 @ X27 )
      | ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X27 ) ) ),
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
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
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
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
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
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
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
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_pre_topc @ X46 @ X45 )
       != ( k2_struct_0 @ X46 ) )
      | ( v1_tops_1 @ X45 @ X46 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
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
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('56',plain,(
    ! [X38: $i] :
      ( ( l1_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v1_tops_1 @ X45 @ X46 )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = ( k2_struct_0 @ X46 ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
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
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup+',[status(thm)],['45','65'])).

thf('67',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('70',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('71',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 ) @ X49 )
      | ( v4_pre_topc @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('75',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('76',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('81',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['67','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('91',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
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

thf('92',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v4_pre_topc @ X39 @ X40 )
      | ( ( k2_pre_topc @ X40 @ X39 )
        = X39 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('101',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('102',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 ) @ X49 )
      | ( v4_pre_topc @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','82'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('110',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v4_pre_topc @ X39 @ X40 )
      | ( ( k2_pre_topc @ X40 @ X39 )
        = X39 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup+',[status(thm)],['99','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('117',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup+',[status(thm)],['98','117'])).

thf('119',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('121',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ k1_xboole_0 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(demod,[status(thm)],['41','119','120'])).

thf('122',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X26 )
      | ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('123',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','82'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('125',plain,(
    ! [X47: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X47 ) @ X47 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('126',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('128',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 ) @ X49 )
      | ( v4_pre_topc @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('136',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v4_pre_topc @ X39 @ X40 )
      | ( ( k2_pre_topc @ X40 @ X39 )
        = X39 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('142',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r2_hidden @ ( sk_D @ X33 @ X31 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ( X33
        = ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('148',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('149',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 ) @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('155',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('156',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k4_xboole_0 @ X8 @ X10 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X26: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X30 )
      | ~ ( r1_xboole_0 @ X29 @ X26 )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ~ ( v3_pre_topc @ X26 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('162',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['146','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v3_pre_topc @ X26 @ X27 )
      | ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('168',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('170',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['139','172'])).

thf('174',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('177',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('179',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('180',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v2_pre_topc @ X40 )
      | ( ( k2_pre_topc @ X40 @ X39 )
       != X39 )
      | ( v4_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['177','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('189',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['124','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','82'])).

thf('194',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('195',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
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

thf('196',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( r2_hidden @ X43 @ ( k2_pre_topc @ X42 @ X41 ) )
      | ~ ( r1_xboole_0 @ X41 @ X44 )
      | ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( v3_pre_topc @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X42 ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['157'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['193','200'])).

thf('202',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','201'])).

thf('203',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['177','186'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('205',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['202','207','208'])).

thf('210',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('211',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['209','212'])).

thf('214',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('215',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( m1_subset_1 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['213','216'])).

thf('218',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(clc,[status(thm)],['123','217'])).

thf('219',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('220',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ! [X50: $i] :
        ( ( X50 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X50 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X50 ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['222'])).

thf('224',plain,
    ( ~ ! [X50: $i] :
          ( ( X50 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X50 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X50 ) )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['221','223'])).

thf('225',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['222'])).

thf('226',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['226'])).

thf('228',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['228'])).

thf('230',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['230'])).

thf('232',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('234',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('238',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('239',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r2_hidden @ ( sk_D @ X33 @ X31 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ( X33
        = ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('240',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( X0
          = ( k2_pre_topc @ sk_A @ sk_C ) )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( X0
          = ( k2_pre_topc @ sk_A @ sk_C ) )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['237','242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('245',plain,
    ( ( ( k1_xboole_0
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_C @ sk_A ) @ k1_xboole_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('247',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( ( k1_xboole_0
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_C @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['245','246','247','248'])).

thf('250',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v3_pre_topc @ X26 @ X27 )
      | ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('251',plain,
    ( ( ( k1_xboole_0
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('253',plain,
    ( ( ( k1_xboole_0
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( ( k1_xboole_0
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('257',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( X0
          = ( k2_pre_topc @ sk_A @ sk_C ) )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('258',plain,
    ( ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('260',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_A ) @ k1_xboole_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('262',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['260','261','262','263'])).

thf('265',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v3_pre_topc @ X26 @ X27 )
      | ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('266',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('268',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['255','270'])).

thf('272',plain,
    ( ( ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('274',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['272','273'])).

thf('275',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('278',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['274','275','276','277'])).

thf('279',plain,
    ( ( ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('281',plain,
    ( ( ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['279','280'])).

thf('282',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['281','282'])).

thf('284',plain,
    ( ( ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ( v4_pre_topc @ k1_xboole_0 @ sk_A )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['278','284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('287',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('290',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['236','289'])).

thf('291',plain,
    ( ( v4_pre_topc @ k1_xboole_0 @ sk_A )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['278','284'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('293',plain,
    ( ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['291','292'])).

thf('294',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('297',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['290','297'])).

thf('299',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('300',plain,(
    ! [X31: $i,X32: $i,X33: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r2_hidden @ ( sk_D @ X33 @ X31 @ X32 ) @ X33 )
      | ~ ( zip_tseitin_0 @ X36 @ ( sk_D @ X33 @ X31 @ X32 ) @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( X33
        = ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('301',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['298','301'])).

thf('303',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('304',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('305',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('306',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['302','303','304','305','306'])).

thf('308',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['226'])).

thf('310',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['222'])).

thf('311',plain,(
    ! [X26: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X30 )
      | ~ ( r1_xboole_0 @ X29 @ X26 )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ~ ( v3_pre_topc @ X26 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('312',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v3_pre_topc @ sk_C @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_C )
        | ( zip_tseitin_0 @ sk_C @ X1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['309','312'])).

thf('314',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_B @ sk_A ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['308','313'])).

thf('315',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('316',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('317',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('318',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('320',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( X33
       != ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X31 @ X32 )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ~ ( r2_hidden @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('321',plain,(
    ! [X31: $i,X32: $i,X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X32 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( r2_hidden @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_hidden @ X35 @ ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_pre_topc @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['319','321'])).

thf('323',plain,
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
    inference('sup-',[status(thm)],['318','322'])).

thf('324',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('325',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('327',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('329',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['323','324','325','326','327','328'])).

thf('330',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['315','329'])).

thf('331',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['314','330'])).

thf('332',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['236','289'])).

thf('333',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['331','332'])).

thf('334',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('335',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['236','289'])).

thf('336',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['334','335'])).

thf('337',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('338',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('339',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['333','338'])).

thf('340',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['228'])).

thf('341',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['339','340'])).

thf('342',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','224','225','227','229','231','342'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pa7CJ6N6UI
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 54.39/54.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 54.39/54.62  % Solved by: fo/fo7.sh
% 54.39/54.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.39/54.62  % done 57712 iterations in 54.157s
% 54.39/54.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 54.39/54.62  % SZS output start Refutation
% 54.39/54.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 54.39/54.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 54.39/54.62  thf(sk_A_type, type, sk_A: $i).
% 54.39/54.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 54.39/54.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 54.39/54.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 54.39/54.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 54.39/54.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 54.39/54.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 54.39/54.62  thf(sk_B_type, type, sk_B: $i).
% 54.39/54.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 54.39/54.62  thf(sk_C_type, type, sk_C: $i).
% 54.39/54.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 54.39/54.62  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 54.39/54.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 54.39/54.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 54.39/54.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 54.39/54.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 54.39/54.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 54.39/54.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 54.39/54.62  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 54.39/54.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 54.39/54.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 54.39/54.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 54.39/54.62  thf(t80_tops_1, conjecture,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 54.39/54.62       ( ![B:$i]:
% 54.39/54.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62           ( ( v1_tops_1 @ B @ A ) <=>
% 54.39/54.62             ( ![C:$i]:
% 54.39/54.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62                 ( ~( ( ( C ) != ( k1_xboole_0 ) ) & ( v3_pre_topc @ C @ A ) & 
% 54.39/54.62                      ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ))).
% 54.39/54.62  thf(zf_stmt_0, negated_conjecture,
% 54.39/54.62    (~( ![A:$i]:
% 54.39/54.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 54.39/54.62          ( ![B:$i]:
% 54.39/54.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62              ( ( v1_tops_1 @ B @ A ) <=>
% 54.39/54.62                ( ![C:$i]:
% 54.39/54.62                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62                    ( ~( ( ( C ) != ( k1_xboole_0 ) ) & 
% 54.39/54.62                         ( v3_pre_topc @ C @ A ) & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ) )),
% 54.39/54.62    inference('cnf.neg', [status(esa)], [t80_tops_1])).
% 54.39/54.62  thf('0', plain,
% 54.39/54.62      (![X50 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ((X50) = (k1_xboole_0))
% 54.39/54.62          | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62          | ~ (r1_xboole_0 @ sk_B @ X50)
% 54.39/54.62          | (v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('1', plain,
% 54.39/54.62      ((![X50 : $i]:
% 54.39/54.62          (((X50) = (k1_xboole_0))
% 54.39/54.62           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62           | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62           | ~ (r1_xboole_0 @ sk_B @ X50))) | 
% 54.39/54.62       ((v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('split', [status(esa)], ['0'])).
% 54.39/54.62  thf(dt_k2_subset_1, axiom,
% 54.39/54.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 54.39/54.62  thf('2', plain,
% 54.39/54.62      (![X14 : $i]: (m1_subset_1 @ (k2_subset_1 @ X14) @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 54.39/54.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 54.39/54.62  thf('3', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 54.39/54.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 54.39/54.62  thf('4', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('5', plain,
% 54.39/54.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf(d13_pre_topc, axiom,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( l1_pre_topc @ A ) =>
% 54.39/54.62       ( ![B:$i]:
% 54.39/54.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62           ( ![C:$i]:
% 54.39/54.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 54.39/54.62                 ( ![D:$i]:
% 54.39/54.62                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 54.39/54.62                     ( ( r2_hidden @ D @ C ) <=>
% 54.39/54.62                       ( ![E:$i]:
% 54.39/54.62                         ( ( m1_subset_1 @
% 54.39/54.62                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62                           ( ~( ( r1_xboole_0 @ B @ E ) & 
% 54.39/54.62                                ( r2_hidden @ D @ E ) & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 54.39/54.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 54.39/54.62  thf(zf_stmt_2, axiom,
% 54.39/54.62    (![E:$i,D:$i,B:$i,A:$i]:
% 54.39/54.62     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 54.39/54.62       ( ( v3_pre_topc @ E @ A ) & ( r2_hidden @ D @ E ) & 
% 54.39/54.62         ( r1_xboole_0 @ B @ E ) ) ))).
% 54.39/54.62  thf(zf_stmt_3, axiom,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( l1_pre_topc @ A ) =>
% 54.39/54.62       ( ![B:$i]:
% 54.39/54.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62           ( ![C:$i]:
% 54.39/54.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 54.39/54.62                 ( ![D:$i]:
% 54.39/54.62                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 54.39/54.62                     ( ( r2_hidden @ D @ C ) <=>
% 54.39/54.62                       ( ![E:$i]:
% 54.39/54.62                         ( ( m1_subset_1 @
% 54.39/54.62                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62                           ( ~( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 54.39/54.62  thf('6', plain,
% 54.39/54.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ~ (r2_hidden @ (sk_D @ X33 @ X31 @ X32) @ X33)
% 54.39/54.62          | (zip_tseitin_0 @ (sk_E @ X33 @ X31 @ X32) @ 
% 54.39/54.62             (sk_D @ X33 @ X31 @ X32) @ X31 @ X32)
% 54.39/54.62          | ((X33) = (k2_pre_topc @ X32 @ X31))
% 54.39/54.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ~ (l1_pre_topc @ X32))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 54.39/54.62  thf('7', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ sk_A)
% 54.39/54.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 54.39/54.62             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 54.39/54.62          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['5', '6'])).
% 54.39/54.62  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('9', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 54.39/54.62             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 54.39/54.62          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['7', '8'])).
% 54.39/54.62  thf('10', plain,
% 54.39/54.62      ((~ (r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62           (u1_struct_0 @ sk_A))
% 54.39/54.62        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 54.39/54.62        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['4', '9'])).
% 54.39/54.62  thf('11', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('12', plain,
% 54.39/54.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('13', plain,
% 54.39/54.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | (r2_hidden @ (sk_D @ X33 @ X31 @ X32) @ (u1_struct_0 @ X32))
% 54.39/54.62          | ((X33) = (k2_pre_topc @ X32 @ X31))
% 54.39/54.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ~ (l1_pre_topc @ X32))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 54.39/54.62  thf('14', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ sk_A)
% 54.39/54.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['12', '13'])).
% 54.39/54.62  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('16', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('demod', [status(thm)], ['14', '15'])).
% 54.39/54.62  thf('17', plain,
% 54.39/54.62      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62         (u1_struct_0 @ sk_A))
% 54.39/54.62        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['11', '16'])).
% 54.39/54.62  thf('18', plain,
% 54.39/54.62      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 54.39/54.62      inference('clc', [status(thm)], ['10', '17'])).
% 54.39/54.62  thf('19', plain,
% 54.39/54.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 54.39/54.62         ((r1_xboole_0 @ X29 @ X26) | ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X27))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.39/54.62  thf('20', plain,
% 54.39/54.62      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['18', '19'])).
% 54.39/54.62  thf('21', plain,
% 54.39/54.62      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62         (u1_struct_0 @ sk_A))
% 54.39/54.62        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['11', '16'])).
% 54.39/54.62  thf('22', plain,
% 54.39/54.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('23', plain,
% 54.39/54.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ~ (r2_hidden @ (sk_D @ X33 @ X31 @ X32) @ X33)
% 54.39/54.62          | (m1_subset_1 @ (sk_E @ X33 @ X31 @ X32) @ 
% 54.39/54.62             (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ((X33) = (k2_pre_topc @ X32 @ X31))
% 54.39/54.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ~ (l1_pre_topc @ X32))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 54.39/54.62  thf('24', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ sk_A)
% 54.39/54.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 54.39/54.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['22', '23'])).
% 54.39/54.62  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('26', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 54.39/54.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['24', '25'])).
% 54.39/54.62  thf('27', plain,
% 54.39/54.62      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['21', '26'])).
% 54.39/54.62  thf('28', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('29', plain,
% 54.39/54.62      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 54.39/54.62      inference('demod', [status(thm)], ['27', '28'])).
% 54.39/54.62  thf('30', plain,
% 54.39/54.62      (((m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 54.39/54.62      inference('simplify', [status(thm)], ['29'])).
% 54.39/54.62  thf('31', plain,
% 54.39/54.62      ((![X50 : $i]:
% 54.39/54.62          (((X50) = (k1_xboole_0))
% 54.39/54.62           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62           | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62           | ~ (r1_xboole_0 @ sk_B @ X50)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('split', [status(esa)], ['0'])).
% 54.39/54.62  thf('32', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | ~ (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A))
% 54.39/54.62         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 54.39/54.62         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['30', '31'])).
% 54.39/54.62  thf('33', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 54.39/54.62         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['20', '32'])).
% 54.39/54.62  thf('34', plain,
% 54.39/54.62      (((~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 54.39/54.62         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['33'])).
% 54.39/54.62  thf('35', plain,
% 54.39/54.62      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 54.39/54.62      inference('clc', [status(thm)], ['10', '17'])).
% 54.39/54.62  thf('36', plain,
% 54.39/54.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 54.39/54.62         ((v3_pre_topc @ X26 @ X27) | ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X27))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.39/54.62  thf('37', plain,
% 54.39/54.62      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['35', '36'])).
% 54.39/54.62  thf('38', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('clc', [status(thm)], ['34', '37'])).
% 54.39/54.62  thf('39', plain,
% 54.39/54.62      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 54.39/54.62      inference('clc', [status(thm)], ['10', '17'])).
% 54.39/54.62  thf('40', plain,
% 54.39/54.62      ((((zip_tseitin_0 @ k1_xboole_0 @ 
% 54.39/54.62          (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup+', [status(thm)], ['38', '39'])).
% 54.39/54.62  thf('41', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | (zip_tseitin_0 @ k1_xboole_0 @ 
% 54.39/54.62            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['40'])).
% 54.39/54.62  thf('42', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('clc', [status(thm)], ['34', '37'])).
% 54.39/54.62  thf('43', plain,
% 54.39/54.62      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62        | (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['35', '36'])).
% 54.39/54.62  thf('44', plain,
% 54.39/54.62      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup+', [status(thm)], ['42', '43'])).
% 54.39/54.62  thf('45', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['44'])).
% 54.39/54.62  thf(d3_struct_0, axiom,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 54.39/54.62  thf('46', plain,
% 54.39/54.62      (![X37 : $i]:
% 54.39/54.62         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.39/54.62  thf('47', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['44'])).
% 54.39/54.62  thf('48', plain,
% 54.39/54.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf(d3_tops_1, axiom,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( l1_pre_topc @ A ) =>
% 54.39/54.62       ( ![B:$i]:
% 54.39/54.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62           ( ( v1_tops_1 @ B @ A ) <=>
% 54.39/54.62             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 54.39/54.62  thf('49', plain,
% 54.39/54.62      (![X45 : $i, X46 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 54.39/54.62          | ((k2_pre_topc @ X46 @ X45) != (k2_struct_0 @ X46))
% 54.39/54.62          | (v1_tops_1 @ X45 @ X46)
% 54.39/54.62          | ~ (l1_pre_topc @ X46))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_tops_1])).
% 54.39/54.62  thf('50', plain,
% 54.39/54.62      ((~ (l1_pre_topc @ sk_A)
% 54.39/54.62        | (v1_tops_1 @ sk_B @ sk_A)
% 54.39/54.62        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['48', '49'])).
% 54.39/54.62  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('52', plain,
% 54.39/54.62      (((v1_tops_1 @ sk_B @ sk_A)
% 54.39/54.62        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 54.39/54.62      inference('demod', [status(thm)], ['50', '51'])).
% 54.39/54.62  thf('53', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 54.39/54.62         | (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v1_tops_1 @ sk_B @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['47', '52'])).
% 54.39/54.62  thf('54', plain,
% 54.39/54.62      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 54.39/54.62         | ~ (l1_struct_0 @ sk_A)
% 54.39/54.62         | (v1_tops_1 @ sk_B @ sk_A)
% 54.39/54.62         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['46', '53'])).
% 54.39/54.62  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf(dt_l1_pre_topc, axiom,
% 54.39/54.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 54.39/54.62  thf('56', plain,
% 54.39/54.62      (![X38 : $i]: ((l1_struct_0 @ X38) | ~ (l1_pre_topc @ X38))),
% 54.39/54.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 54.39/54.62  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('58', plain,
% 54.39/54.62      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 54.39/54.62         | (v1_tops_1 @ sk_B @ sk_A)
% 54.39/54.62         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('demod', [status(thm)], ['54', '57'])).
% 54.39/54.62  thf('59', plain,
% 54.39/54.62      ((((v3_pre_topc @ k1_xboole_0 @ sk_A) | (v1_tops_1 @ sk_B @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['58'])).
% 54.39/54.62  thf('60', plain,
% 54.39/54.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('61', plain,
% 54.39/54.62      (![X45 : $i, X46 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 54.39/54.62          | ~ (v1_tops_1 @ X45 @ X46)
% 54.39/54.62          | ((k2_pre_topc @ X46 @ X45) = (k2_struct_0 @ X46))
% 54.39/54.62          | ~ (l1_pre_topc @ X46))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_tops_1])).
% 54.39/54.62  thf('62', plain,
% 54.39/54.62      ((~ (l1_pre_topc @ sk_A)
% 54.39/54.62        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 54.39/54.62        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['60', '61'])).
% 54.39/54.62  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('64', plain,
% 54.39/54.62      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 54.39/54.62        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('demod', [status(thm)], ['62', '63'])).
% 54.39/54.62  thf('65', plain,
% 54.39/54.62      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['59', '64'])).
% 54.39/54.62  thf('66', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup+', [status(thm)], ['45', '65'])).
% 54.39/54.62  thf('67', plain,
% 54.39/54.62      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['66'])).
% 54.39/54.62  thf('68', plain,
% 54.39/54.62      (![X37 : $i]:
% 54.39/54.62         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.39/54.62  thf('69', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('70', plain,
% 54.39/54.62      (![X37 : $i]:
% 54.39/54.62         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.39/54.62  thf(t29_tops_1, axiom,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( l1_pre_topc @ A ) =>
% 54.39/54.62       ( ![B:$i]:
% 54.39/54.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62           ( ( v4_pre_topc @ B @ A ) <=>
% 54.39/54.62             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 54.39/54.62  thf('71', plain,
% 54.39/54.62      (![X48 : $i, X49 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 54.39/54.62          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X49) @ X48) @ X49)
% 54.39/54.62          | (v4_pre_topc @ X48 @ X49)
% 54.39/54.62          | ~ (l1_pre_topc @ X49))),
% 54.39/54.62      inference('cnf', [status(esa)], [t29_tops_1])).
% 54.39/54.62  thf('72', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ X1 @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['70', '71'])).
% 54.39/54.62  thf('73', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (v3_pre_topc @ 
% 54.39/54.62             (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ X0)
% 54.39/54.62          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['69', '72'])).
% 54.39/54.62  thf('74', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (v3_pre_topc @ 
% 54.39/54.62             (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['68', '73'])).
% 54.39/54.62  thf(t4_subset_1, axiom,
% 54.39/54.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 54.39/54.62  thf('75', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf(involutiveness_k3_subset_1, axiom,
% 54.39/54.62    (![A:$i,B:$i]:
% 54.39/54.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.39/54.62       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 54.39/54.62  thf('76', plain,
% 54.39/54.62      (![X15 : $i, X16 : $i]:
% 54.39/54.62         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 54.39/54.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 54.39/54.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 54.39/54.62  thf('77', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['75', '76'])).
% 54.39/54.62  thf('78', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf(d5_subset_1, axiom,
% 54.39/54.62    (![A:$i,B:$i]:
% 54.39/54.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.39/54.62       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 54.39/54.62  thf('79', plain,
% 54.39/54.62      (![X12 : $i, X13 : $i]:
% 54.39/54.62         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 54.39/54.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 54.39/54.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 54.39/54.62  thf('80', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['78', '79'])).
% 54.39/54.62  thf(t3_boole, axiom,
% 54.39/54.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 54.39/54.62  thf('81', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 54.39/54.62      inference('cnf', [status(esa)], [t3_boole])).
% 54.39/54.62  thf('82', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 54.39/54.62      inference('sup+', [status(thm)], ['80', '81'])).
% 54.39/54.62  thf('83', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 54.39/54.62      inference('demod', [status(thm)], ['77', '82'])).
% 54.39/54.62  thf('84', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['74', '83'])).
% 54.39/54.62  thf('85', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         ((v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('simplify', [status(thm)], ['84'])).
% 54.39/54.62  thf('86', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | ~ (l1_struct_0 @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)
% 54.39/54.62         | (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['67', '85'])).
% 54.39/54.62  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('89', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('demod', [status(thm)], ['86', '87', '88'])).
% 54.39/54.62  thf('90', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('91', plain,
% 54.39/54.62      (![X37 : $i]:
% 54.39/54.62         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.39/54.62  thf(t52_pre_topc, axiom,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( l1_pre_topc @ A ) =>
% 54.39/54.62       ( ![B:$i]:
% 54.39/54.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 54.39/54.62             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 54.39/54.62               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 54.39/54.62  thf('92', plain,
% 54.39/54.62      (![X39 : $i, X40 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 54.39/54.62          | ~ (v4_pre_topc @ X39 @ X40)
% 54.39/54.62          | ((k2_pre_topc @ X40 @ X39) = (X39))
% 54.39/54.62          | ~ (l1_pre_topc @ X40))),
% 54.39/54.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 54.39/54.62  thf('93', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 54.39/54.62          | ~ (v4_pre_topc @ X1 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['91', '92'])).
% 54.39/54.62  thf('94', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 54.39/54.62          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['90', '93'])).
% 54.39/54.62  thf('95', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | ~ (l1_struct_0 @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)
% 54.39/54.62         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['89', '94'])).
% 54.39/54.62  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('98', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('demod', [status(thm)], ['95', '96', '97'])).
% 54.39/54.62  thf('99', plain,
% 54.39/54.62      (![X37 : $i]:
% 54.39/54.62         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.39/54.62  thf('100', plain,
% 54.39/54.62      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['66'])).
% 54.39/54.62  thf('101', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('102', plain,
% 54.39/54.62      (![X48 : $i, X49 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 54.39/54.62          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X49) @ X48) @ X49)
% 54.39/54.62          | (v4_pre_topc @ X48 @ X49)
% 54.39/54.62          | ~ (l1_pre_topc @ X49))),
% 54.39/54.62      inference('cnf', [status(esa)], [t29_tops_1])).
% 54.39/54.62  thf('103', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ 
% 54.39/54.62               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['101', '102'])).
% 54.39/54.62  thf('104', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 54.39/54.62      inference('demod', [status(thm)], ['77', '82'])).
% 54.39/54.62  thf('105', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['103', '104'])).
% 54.39/54.62  thf('106', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['100', '105'])).
% 54.39/54.62  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('108', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('demod', [status(thm)], ['106', '107'])).
% 54.39/54.62  thf('109', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('110', plain,
% 54.39/54.62      (![X39 : $i, X40 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 54.39/54.62          | ~ (v4_pre_topc @ X39 @ X40)
% 54.39/54.62          | ((k2_pre_topc @ X40 @ X39) = (X39))
% 54.39/54.62          | ~ (l1_pre_topc @ X40))),
% 54.39/54.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 54.39/54.62  thf('111', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 54.39/54.62          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['109', '110'])).
% 54.39/54.62  thf('112', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['108', '111'])).
% 54.39/54.62  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('114', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('demod', [status(thm)], ['112', '113'])).
% 54.39/54.62  thf('115', plain,
% 54.39/54.62      (((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 54.39/54.62         | ~ (l1_struct_0 @ sk_A)
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup+', [status(thm)], ['99', '114'])).
% 54.39/54.62  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('117', plain,
% 54.39/54.62      (((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('demod', [status(thm)], ['115', '116'])).
% 54.39/54.62  thf('118', plain,
% 54.39/54.62      (((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup+', [status(thm)], ['98', '117'])).
% 54.39/54.62  thf('119', plain,
% 54.39/54.62      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['118'])).
% 54.39/54.62  thf('120', plain,
% 54.39/54.62      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['118'])).
% 54.39/54.62  thf('121', plain,
% 54.39/54.62      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | (zip_tseitin_0 @ k1_xboole_0 @ 
% 54.39/54.62            (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('demod', [status(thm)], ['41', '119', '120'])).
% 54.39/54.62  thf('122', plain,
% 54.39/54.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 54.39/54.62         ((r2_hidden @ X28 @ X26) | ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X27))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.39/54.62  thf('123', plain,
% 54.39/54.62      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.62         | (r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 54.39/54.62            k1_xboole_0)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['121', '122'])).
% 54.39/54.62  thf('124', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 54.39/54.62      inference('demod', [status(thm)], ['77', '82'])).
% 54.39/54.62  thf(fc10_tops_1, axiom,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 54.39/54.62       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 54.39/54.62  thf('125', plain,
% 54.39/54.62      (![X47 : $i]:
% 54.39/54.62         ((v3_pre_topc @ (k2_struct_0 @ X47) @ X47)
% 54.39/54.62          | ~ (l1_pre_topc @ X47)
% 54.39/54.62          | ~ (v2_pre_topc @ X47))),
% 54.39/54.62      inference('cnf', [status(esa)], [fc10_tops_1])).
% 54.39/54.62  thf('126', plain,
% 54.39/54.62      (![X37 : $i]:
% 54.39/54.62         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.39/54.62  thf('127', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf('128', plain,
% 54.39/54.62      (![X48 : $i, X49 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 54.39/54.62          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X49) @ X48) @ X49)
% 54.39/54.62          | (v4_pre_topc @ X48 @ X49)
% 54.39/54.62          | ~ (l1_pre_topc @ X49))),
% 54.39/54.62      inference('cnf', [status(esa)], [t29_tops_1])).
% 54.39/54.62  thf('129', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ 
% 54.39/54.62               (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['127', '128'])).
% 54.39/54.62  thf('130', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 54.39/54.62      inference('sup+', [status(thm)], ['80', '81'])).
% 54.39/54.62  thf('131', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['129', '130'])).
% 54.39/54.62  thf('132', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['126', '131'])).
% 54.39/54.62  thf('133', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (v2_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['125', '132'])).
% 54.39/54.62  thf('134', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_struct_0 @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (v2_pre_topc @ X0))),
% 54.39/54.62      inference('simplify', [status(thm)], ['133'])).
% 54.39/54.62  thf('135', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf('136', plain,
% 54.39/54.62      (![X39 : $i, X40 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 54.39/54.62          | ~ (v4_pre_topc @ X39 @ X40)
% 54.39/54.62          | ((k2_pre_topc @ X40 @ X39) = (X39))
% 54.39/54.62          | ~ (l1_pre_topc @ X40))),
% 54.39/54.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 54.39/54.62  thf('137', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 54.39/54.62          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['135', '136'])).
% 54.39/54.62  thf('138', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (v2_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 54.39/54.62          | ~ (l1_pre_topc @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['134', '137'])).
% 54.39/54.62  thf('139', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (v2_pre_topc @ X0))),
% 54.39/54.62      inference('simplify', [status(thm)], ['138'])).
% 54.39/54.62  thf('140', plain,
% 54.39/54.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('141', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf('142', plain,
% 54.39/54.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | (r2_hidden @ (sk_D @ X33 @ X31 @ X32) @ (u1_struct_0 @ X32))
% 54.39/54.62          | ((X33) = (k2_pre_topc @ X32 @ X31))
% 54.39/54.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ~ (l1_pre_topc @ X32))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 54.39/54.62  thf('143', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.39/54.62          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 54.39/54.62          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['141', '142'])).
% 54.39/54.62  thf('144', plain,
% 54.39/54.62      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.39/54.62        | ((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62        | ~ (l1_pre_topc @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['140', '143'])).
% 54.39/54.62  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('146', plain,
% 54.39/54.62      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.39/54.62        | ((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0)))),
% 54.39/54.62      inference('demod', [status(thm)], ['144', '145'])).
% 54.39/54.62  thf('147', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_struct_0 @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (v2_pre_topc @ X0))),
% 54.39/54.62      inference('simplify', [status(thm)], ['133'])).
% 54.39/54.62  thf('148', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf('149', plain,
% 54.39/54.62      (![X48 : $i, X49 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 54.39/54.62          | ~ (v4_pre_topc @ X48 @ X49)
% 54.39/54.62          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X49) @ X48) @ X49)
% 54.39/54.62          | ~ (l1_pre_topc @ X49))),
% 54.39/54.62      inference('cnf', [status(esa)], [t29_tops_1])).
% 54.39/54.62  thf('150', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 54.39/54.62             X0)
% 54.39/54.62          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['148', '149'])).
% 54.39/54.62  thf('151', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 54.39/54.62      inference('sup+', [status(thm)], ['80', '81'])).
% 54.39/54.62  thf('152', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['150', '151'])).
% 54.39/54.62  thf('153', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (v2_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['147', '152'])).
% 54.39/54.62  thf('154', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (v2_pre_topc @ X0))),
% 54.39/54.62      inference('simplify', [status(thm)], ['153'])).
% 54.39/54.62  thf(t4_boole, axiom,
% 54.39/54.62    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 54.39/54.62  thf('155', plain,
% 54.39/54.62      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_boole])).
% 54.39/54.62  thf(t83_xboole_1, axiom,
% 54.39/54.62    (![A:$i,B:$i]:
% 54.39/54.62     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 54.39/54.62  thf('156', plain,
% 54.39/54.62      (![X8 : $i, X10 : $i]:
% 54.39/54.62         ((r1_xboole_0 @ X8 @ X10) | ((k4_xboole_0 @ X8 @ X10) != (X8)))),
% 54.39/54.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 54.39/54.62  thf('157', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['155', '156'])).
% 54.39/54.62  thf('158', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 54.39/54.62      inference('simplify', [status(thm)], ['157'])).
% 54.39/54.62  thf('159', plain,
% 54.39/54.62      (![X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 54.39/54.62         ((zip_tseitin_0 @ X26 @ X28 @ X29 @ X30)
% 54.39/54.62          | ~ (r1_xboole_0 @ X29 @ X26)
% 54.39/54.62          | ~ (r2_hidden @ X28 @ X26)
% 54.39/54.62          | ~ (v3_pre_topc @ X26 @ X30))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.39/54.62  thf('160', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.39/54.62         (~ (v3_pre_topc @ X0 @ X1)
% 54.39/54.62          | ~ (r2_hidden @ X2 @ X0)
% 54.39/54.62          | (zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1))),
% 54.39/54.62      inference('sup-', [status(thm)], ['158', '159'])).
% 54.39/54.62  thf('161', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         (~ (v2_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['154', '160'])).
% 54.39/54.62  thf('162', plain,
% 54.39/54.62      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62        | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62           (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)
% 54.39/54.62        | ~ (l1_struct_0 @ sk_A)
% 54.39/54.62        | ~ (l1_pre_topc @ sk_A)
% 54.39/54.62        | ~ (v2_pre_topc @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['146', '161'])).
% 54.39/54.62  thf('163', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('165', plain, ((v2_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('166', plain,
% 54.39/54.62      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62        | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62           (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A))),
% 54.39/54.62      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 54.39/54.62  thf('167', plain,
% 54.39/54.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 54.39/54.62         ((v3_pre_topc @ X26 @ X27) | ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X27))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.39/54.62  thf('168', plain,
% 54.39/54.62      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['166', '167'])).
% 54.39/54.62  thf('169', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['129', '130'])).
% 54.39/54.62  thf('170', plain,
% 54.39/54.62      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62        | ~ (l1_pre_topc @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['168', '169'])).
% 54.39/54.62  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('172', plain,
% 54.39/54.62      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 54.39/54.62      inference('demod', [status(thm)], ['170', '171'])).
% 54.39/54.62  thf('173', plain,
% 54.39/54.62      ((((sk_B) = (k1_xboole_0))
% 54.39/54.62        | ~ (v2_pre_topc @ sk_A)
% 54.39/54.62        | ~ (l1_pre_topc @ sk_A)
% 54.39/54.62        | ~ (l1_struct_0 @ sk_A)
% 54.39/54.62        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 54.39/54.62      inference('sup+', [status(thm)], ['139', '172'])).
% 54.39/54.62  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('176', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('177', plain,
% 54.39/54.62      ((((sk_B) = (k1_xboole_0)) | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 54.39/54.62      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 54.39/54.62  thf('178', plain,
% 54.39/54.62      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 54.39/54.62      inference('demod', [status(thm)], ['170', '171'])).
% 54.39/54.62  thf('179', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf('180', plain,
% 54.39/54.62      (![X39 : $i, X40 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 54.39/54.62          | ~ (v2_pre_topc @ X40)
% 54.39/54.62          | ((k2_pre_topc @ X40 @ X39) != (X39))
% 54.39/54.62          | (v4_pre_topc @ X39 @ X40)
% 54.39/54.62          | ~ (l1_pre_topc @ X40))),
% 54.39/54.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 54.39/54.62  thf('181', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ((k2_pre_topc @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 54.39/54.62          | ~ (v2_pre_topc @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['179', '180'])).
% 54.39/54.62  thf('182', plain,
% 54.39/54.62      ((((sk_B) != (k1_xboole_0))
% 54.39/54.62        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62        | ~ (v2_pre_topc @ sk_A)
% 54.39/54.62        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62        | ~ (l1_pre_topc @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['178', '181'])).
% 54.39/54.62  thf('183', plain, ((v2_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('184', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('185', plain,
% 54.39/54.62      ((((sk_B) != (k1_xboole_0))
% 54.39/54.62        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 54.39/54.62      inference('demod', [status(thm)], ['182', '183', '184'])).
% 54.39/54.62  thf('186', plain,
% 54.39/54.62      (((v4_pre_topc @ k1_xboole_0 @ sk_A) | ((sk_B) != (k1_xboole_0)))),
% 54.39/54.62      inference('simplify', [status(thm)], ['185'])).
% 54.39/54.62  thf('187', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 54.39/54.62      inference('clc', [status(thm)], ['177', '186'])).
% 54.39/54.62  thf('188', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 54.39/54.62          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['135', '136'])).
% 54.39/54.62  thf('189', plain,
% 54.39/54.62      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 54.39/54.62        | ~ (l1_pre_topc @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['187', '188'])).
% 54.39/54.62  thf('190', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('191', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 54.39/54.62      inference('demod', [status(thm)], ['189', '190'])).
% 54.39/54.62  thf('192', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         ((k2_pre_topc @ sk_A @ (k3_subset_1 @ X0 @ X0)) = (k1_xboole_0))),
% 54.39/54.62      inference('sup+', [status(thm)], ['124', '191'])).
% 54.39/54.62  thf('193', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 54.39/54.62      inference('demod', [status(thm)], ['77', '82'])).
% 54.39/54.62  thf('194', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('195', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf(t54_pre_topc, axiom,
% 54.39/54.62    (![A:$i]:
% 54.39/54.62     ( ( l1_pre_topc @ A ) =>
% 54.39/54.62       ( ![B:$i]:
% 54.39/54.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62           ( ![C:$i]:
% 54.39/54.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 54.39/54.62               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 54.39/54.62                 ( ( ~( v2_struct_0 @ A ) ) & 
% 54.39/54.62                   ( ![D:$i]:
% 54.39/54.62                     ( ( m1_subset_1 @
% 54.39/54.62                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.39/54.62                       ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 54.39/54.62                            ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 54.39/54.62  thf('196', plain,
% 54.39/54.62      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 54.39/54.62          | ~ (r2_hidden @ X43 @ (k2_pre_topc @ X42 @ X41))
% 54.39/54.62          | ~ (r1_xboole_0 @ X41 @ X44)
% 54.39/54.62          | ~ (r2_hidden @ X43 @ X44)
% 54.39/54.62          | ~ (v3_pre_topc @ X44 @ X42)
% 54.39/54.62          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 54.39/54.62          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X42))
% 54.39/54.62          | ~ (l1_pre_topc @ X42))),
% 54.39/54.62      inference('cnf', [status(esa)], [t54_pre_topc])).
% 54.39/54.62  thf('197', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 54.39/54.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.39/54.62          | ~ (v3_pre_topc @ X2 @ X0)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ X2)
% 54.39/54.62          | ~ (r1_xboole_0 @ k1_xboole_0 @ X2)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['195', '196'])).
% 54.39/54.62  thf('198', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 54.39/54.62      inference('simplify', [status(thm)], ['157'])).
% 54.39/54.62  thf('199', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 54.39/54.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.39/54.62          | ~ (v3_pre_topc @ X2 @ X0)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ X2)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 54.39/54.62      inference('demod', [status(thm)], ['197', '198'])).
% 54.39/54.62  thf('200', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         (~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0))
% 54.39/54.62          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 54.39/54.62          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 54.39/54.62          | ~ (l1_pre_topc @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['194', '199'])).
% 54.39/54.62  thf('201', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.39/54.62         (~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ (k3_subset_1 @ X0 @ X0)))
% 54.39/54.62          | ~ (l1_pre_topc @ X1)
% 54.39/54.62          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 54.39/54.62          | ~ (v3_pre_topc @ (u1_struct_0 @ X1) @ X1)
% 54.39/54.62          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X1)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['193', '200'])).
% 54.39/54.62  thf('202', plain,
% 54.39/54.62      (![X1 : $i]:
% 54.39/54.62         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 54.39/54.62          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 54.39/54.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 54.39/54.62          | ~ (l1_pre_topc @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['192', '201'])).
% 54.39/54.62  thf('203', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 54.39/54.62      inference('clc', [status(thm)], ['177', '186'])).
% 54.39/54.62  thf('204', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['150', '151'])).
% 54.39/54.62  thf('205', plain,
% 54.39/54.62      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['203', '204'])).
% 54.39/54.62  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('207', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 54.39/54.62      inference('demod', [status(thm)], ['205', '206'])).
% 54.39/54.62  thf('208', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('209', plain,
% 54.39/54.62      (![X1 : $i]:
% 54.39/54.62         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 54.39/54.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 54.39/54.62      inference('demod', [status(thm)], ['202', '207', '208'])).
% 54.39/54.62  thf('210', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf(l3_subset_1, axiom,
% 54.39/54.62    (![A:$i,B:$i]:
% 54.39/54.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.39/54.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 54.39/54.62  thf('211', plain,
% 54.39/54.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 54.39/54.62         (~ (r2_hidden @ X17 @ X18)
% 54.39/54.62          | (r2_hidden @ X17 @ X19)
% 54.39/54.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 54.39/54.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 54.39/54.62  thf('212', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['210', '211'])).
% 54.39/54.62  thf('213', plain,
% 54.39/54.62      (![X1 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 54.39/54.62          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 54.39/54.62      inference('clc', [status(thm)], ['209', '212'])).
% 54.39/54.62  thf('214', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf(t4_subset, axiom,
% 54.39/54.62    (![A:$i,B:$i,C:$i]:
% 54.39/54.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 54.39/54.62       ( m1_subset_1 @ A @ C ) ))).
% 54.39/54.62  thf('215', plain,
% 54.39/54.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 54.39/54.62         (~ (r2_hidden @ X23 @ X24)
% 54.39/54.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 54.39/54.62          | (m1_subset_1 @ X23 @ X25))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset])).
% 54.39/54.62  thf('216', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['214', '215'])).
% 54.39/54.62  thf('217', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 54.39/54.62      inference('clc', [status(thm)], ['213', '216'])).
% 54.39/54.62  thf('218', plain,
% 54.39/54.62      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('clc', [status(thm)], ['123', '217'])).
% 54.39/54.62  thf('219', plain,
% 54.39/54.62      (((v1_tops_1 @ sk_B @ sk_A)
% 54.39/54.62        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 54.39/54.62      inference('demod', [status(thm)], ['50', '51'])).
% 54.39/54.62  thf('220', plain,
% 54.39/54.62      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 54.39/54.62         | (v1_tops_1 @ sk_B @ sk_A)))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['218', '219'])).
% 54.39/54.62  thf('221', plain,
% 54.39/54.62      (((v1_tops_1 @ sk_B @ sk_A))
% 54.39/54.62         <= ((![X50 : $i]:
% 54.39/54.62                (((X50) = (k1_xboole_0))
% 54.39/54.62                 | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62                 | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62                 | ~ (r1_xboole_0 @ sk_B @ X50))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['220'])).
% 54.39/54.62  thf('222', plain,
% 54.39/54.62      (((r1_xboole_0 @ sk_B @ sk_C) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('223', plain,
% 54.39/54.62      ((~ (v1_tops_1 @ sk_B @ sk_A)) <= (~ ((v1_tops_1 @ sk_B @ sk_A)))),
% 54.39/54.62      inference('split', [status(esa)], ['222'])).
% 54.39/54.62  thf('224', plain,
% 54.39/54.62      (~
% 54.39/54.62       (![X50 : $i]:
% 54.39/54.62          (((X50) = (k1_xboole_0))
% 54.39/54.62           | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62           | ~ (v3_pre_topc @ X50 @ sk_A)
% 54.39/54.62           | ~ (r1_xboole_0 @ sk_B @ X50))) | 
% 54.39/54.62       ((v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('sup-', [status(thm)], ['221', '223'])).
% 54.39/54.62  thf('225', plain,
% 54.39/54.62      (((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('split', [status(esa)], ['222'])).
% 54.39/54.62  thf('226', plain,
% 54.39/54.62      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('227', plain,
% 54.39/54.62      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('split', [status(esa)], ['226'])).
% 54.39/54.62  thf('228', plain,
% 54.39/54.62      ((((sk_C) != (k1_xboole_0)) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('229', plain,
% 54.39/54.62      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('split', [status(esa)], ['228'])).
% 54.39/54.62  thf('230', plain,
% 54.39/54.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('231', plain,
% 54.39/54.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 54.39/54.62       ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('split', [status(esa)], ['230'])).
% 54.39/54.62  thf('232', plain,
% 54.39/54.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('split', [status(esa)], ['230'])).
% 54.39/54.62  thf('233', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.39/54.62          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 54.39/54.62          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['141', '142'])).
% 54.39/54.62  thf('234', plain,
% 54.39/54.62      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.39/54.62         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['232', '233'])).
% 54.39/54.62  thf('235', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('236', plain,
% 54.39/54.62      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.39/54.62         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['234', '235'])).
% 54.39/54.62  thf('237', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf('238', plain,
% 54.39/54.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('split', [status(esa)], ['230'])).
% 54.39/54.62  thf('239', plain,
% 54.39/54.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | (r2_hidden @ (sk_D @ X33 @ X31 @ X32) @ (u1_struct_0 @ X32))
% 54.39/54.62          | ((X33) = (k2_pre_topc @ X32 @ X31))
% 54.39/54.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ~ (l1_pre_topc @ X32))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 54.39/54.62  thf('240', plain,
% 54.39/54.62      ((![X0 : $i]:
% 54.39/54.62          (~ (l1_pre_topc @ sk_A)
% 54.39/54.62           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62           | ((X0) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62           | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['238', '239'])).
% 54.39/54.62  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('242', plain,
% 54.39/54.62      ((![X0 : $i]:
% 54.39/54.62          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62           | ((X0) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62           | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['240', '241'])).
% 54.39/54.62  thf('243', plain,
% 54.39/54.62      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.39/54.62         | ((k1_xboole_0) = (k2_pre_topc @ sk_A @ sk_C))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['237', '242'])).
% 54.39/54.62  thf('244', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         (~ (v2_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['154', '160'])).
% 54.39/54.62  thf('245', plain,
% 54.39/54.62      (((((k1_xboole_0) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62            (sk_D @ k1_xboole_0 @ sk_C @ sk_A) @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ~ (l1_struct_0 @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)
% 54.39/54.62         | ~ (v2_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['243', '244'])).
% 54.39/54.62  thf('246', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('247', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('248', plain, ((v2_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('249', plain,
% 54.39/54.62      (((((k1_xboole_0) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62            (sk_D @ k1_xboole_0 @ sk_C @ sk_A) @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['245', '246', '247', '248'])).
% 54.39/54.62  thf('250', plain,
% 54.39/54.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 54.39/54.62         ((v3_pre_topc @ X26 @ X27) | ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X27))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.39/54.62  thf('251', plain,
% 54.39/54.62      (((((k1_xboole_0) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['249', '250'])).
% 54.39/54.62  thf('252', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['129', '130'])).
% 54.39/54.62  thf('253', plain,
% 54.39/54.62      (((((k1_xboole_0) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['251', '252'])).
% 54.39/54.62  thf('254', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('255', plain,
% 54.39/54.62      (((((k1_xboole_0) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['253', '254'])).
% 54.39/54.62  thf('256', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('257', plain,
% 54.39/54.62      ((![X0 : $i]:
% 54.39/54.62          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62           | ((X0) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62           | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['240', '241'])).
% 54.39/54.62  thf('258', plain,
% 54.39/54.62      ((((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_C @ sk_A) @ 
% 54.39/54.62          (u1_struct_0 @ sk_A))
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['256', '257'])).
% 54.39/54.62  thf('259', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i]:
% 54.39/54.62         (~ (v2_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['154', '160'])).
% 54.39/54.62  thf('260', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62            (sk_D @ (u1_struct_0 @ sk_A) @ sk_C @ sk_A) @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ~ (l1_struct_0 @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)
% 54.39/54.62         | ~ (v2_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['258', '259'])).
% 54.39/54.62  thf('261', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('262', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('263', plain, ((v2_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('264', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62            (sk_D @ (u1_struct_0 @ sk_A) @ sk_C @ sk_A) @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['260', '261', '262', '263'])).
% 54.39/54.62  thf('265', plain,
% 54.39/54.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 54.39/54.62         ((v3_pre_topc @ X26 @ X27) | ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X27))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.39/54.62  thf('266', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['264', '265'])).
% 54.39/54.62  thf('267', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['129', '130'])).
% 54.39/54.62  thf('268', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['266', '267'])).
% 54.39/54.62  thf('269', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('270', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C))
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['268', '269'])).
% 54.39/54.62  thf('271', plain,
% 54.39/54.62      (((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup+', [status(thm)], ['255', '270'])).
% 54.39/54.62  thf('272', plain,
% 54.39/54.62      ((((v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['271'])).
% 54.39/54.62  thf('273', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (l1_struct_0 @ X0)
% 54.39/54.62          | ~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (v2_pre_topc @ X0))),
% 54.39/54.62      inference('simplify', [status(thm)], ['153'])).
% 54.39/54.62  thf('274', plain,
% 54.39/54.62      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ~ (v2_pre_topc @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)
% 54.39/54.62         | ~ (l1_struct_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup+', [status(thm)], ['272', '273'])).
% 54.39/54.62  thf('275', plain, ((v2_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('276', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('277', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.62      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.62  thf('278', plain,
% 54.39/54.62      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['274', '275', '276', '277'])).
% 54.39/54.62  thf('279', plain,
% 54.39/54.62      ((((v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['271'])).
% 54.39/54.62  thf('280', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 54.39/54.62          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['129', '130'])).
% 54.39/54.62  thf('281', plain,
% 54.39/54.62      (((~ (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['279', '280'])).
% 54.39/54.62  thf('282', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('283', plain,
% 54.39/54.62      (((~ (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | (v4_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['281', '282'])).
% 54.39/54.62  thf('284', plain,
% 54.39/54.62      ((((v4_pre_topc @ k1_xboole_0 @ sk_A)
% 54.39/54.62         | ~ (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['283'])).
% 54.39/54.62  thf('285', plain,
% 54.39/54.62      (((v4_pre_topc @ k1_xboole_0 @ sk_A))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('clc', [status(thm)], ['278', '284'])).
% 54.39/54.62  thf('286', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 54.39/54.62          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('sup-', [status(thm)], ['135', '136'])).
% 54.39/54.62  thf('287', plain,
% 54.39/54.62      (((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['285', '286'])).
% 54.39/54.62  thf('288', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('289', plain,
% 54.39/54.62      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['287', '288'])).
% 54.39/54.62  thf('290', plain,
% 54.39/54.62      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.39/54.62         | ((sk_C) = (k1_xboole_0))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['236', '289'])).
% 54.39/54.62  thf('291', plain,
% 54.39/54.62      (((v4_pre_topc @ k1_xboole_0 @ sk_A))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('clc', [status(thm)], ['278', '284'])).
% 54.39/54.62  thf('292', plain,
% 54.39/54.62      (![X0 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 54.39/54.62          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 54.39/54.62      inference('demod', [status(thm)], ['150', '151'])).
% 54.39/54.62  thf('293', plain,
% 54.39/54.62      ((((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['291', '292'])).
% 54.39/54.62  thf('294', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('295', plain,
% 54.39/54.62      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['293', '294'])).
% 54.39/54.62  thf('296', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.39/54.62         (~ (v3_pre_topc @ X0 @ X1)
% 54.39/54.62          | ~ (r2_hidden @ X2 @ X0)
% 54.39/54.62          | (zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1))),
% 54.39/54.62      inference('sup-', [status(thm)], ['158', '159'])).
% 54.39/54.62  thf('297', plain,
% 54.39/54.62      ((![X0 : $i]:
% 54.39/54.62          ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0 @ sk_A)
% 54.39/54.62           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['295', '296'])).
% 54.39/54.62  thf('298', plain,
% 54.39/54.62      (((((sk_C) = (k1_xboole_0))
% 54.39/54.62         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62            (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['290', '297'])).
% 54.39/54.62  thf('299', plain,
% 54.39/54.62      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 54.39/54.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.39/54.62  thf('300', plain,
% 54.39/54.62      (![X31 : $i, X32 : $i, X33 : $i, X36 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | (r2_hidden @ (sk_D @ X33 @ X31 @ X32) @ X33)
% 54.39/54.62          | ~ (zip_tseitin_0 @ X36 @ (sk_D @ X33 @ X31 @ X32) @ X31 @ X32)
% 54.39/54.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ((X33) = (k2_pre_topc @ X32 @ X31))
% 54.39/54.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.62          | ~ (l1_pre_topc @ X32))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 54.39/54.62  thf('301', plain,
% 54.39/54.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.39/54.62         (~ (l1_pre_topc @ X0)
% 54.39/54.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.39/54.62          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 54.39/54.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.39/54.62          | ~ (zip_tseitin_0 @ X2 @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 54.39/54.62               k1_xboole_0 @ X0)
% 54.39/54.62          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 54.39/54.62      inference('sup-', [status(thm)], ['299', '300'])).
% 54.39/54.62  thf('302', plain,
% 54.39/54.62      (((((sk_C) = (k1_xboole_0))
% 54.39/54.62         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 54.39/54.62         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.39/54.62              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 54.39/54.62         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.62         | ~ (l1_pre_topc @ sk_A)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['298', '301'])).
% 54.39/54.62  thf('303', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.62      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.62  thf('304', plain,
% 54.39/54.62      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0)))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['287', '288'])).
% 54.39/54.62  thf('305', plain,
% 54.39/54.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('split', [status(esa)], ['230'])).
% 54.39/54.62  thf('306', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.62  thf('307', plain,
% 54.39/54.62      (((((sk_C) = (k1_xboole_0))
% 54.39/54.62         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 54.39/54.62         | ((sk_C) = (k1_xboole_0))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('demod', [status(thm)], ['302', '303', '304', '305', '306'])).
% 54.39/54.62  thf('308', plain,
% 54.39/54.62      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 54.39/54.62         | ((sk_C) = (k1_xboole_0))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('simplify', [status(thm)], ['307'])).
% 54.39/54.62  thf('309', plain,
% 54.39/54.62      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 54.39/54.62      inference('split', [status(esa)], ['226'])).
% 54.39/54.62  thf('310', plain,
% 54.39/54.62      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 54.39/54.62      inference('split', [status(esa)], ['222'])).
% 54.39/54.62  thf('311', plain,
% 54.39/54.62      (![X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 54.39/54.62         ((zip_tseitin_0 @ X26 @ X28 @ X29 @ X30)
% 54.39/54.62          | ~ (r1_xboole_0 @ X29 @ X26)
% 54.39/54.62          | ~ (r2_hidden @ X28 @ X26)
% 54.39/54.62          | ~ (v3_pre_topc @ X26 @ X30))),
% 54.39/54.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.39/54.62  thf('312', plain,
% 54.39/54.62      ((![X0 : $i, X1 : $i]:
% 54.39/54.62          (~ (v3_pre_topc @ sk_C @ X0)
% 54.39/54.62           | ~ (r2_hidden @ X1 @ sk_C)
% 54.39/54.62           | (zip_tseitin_0 @ sk_C @ X1 @ sk_B @ X0)))
% 54.39/54.62         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['310', '311'])).
% 54.39/54.62  thf('313', plain,
% 54.39/54.62      ((![X0 : $i]:
% 54.39/54.62          ((zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A)
% 54.39/54.62           | ~ (r2_hidden @ X0 @ sk_C)))
% 54.39/54.62         <= (((r1_xboole_0 @ sk_B @ sk_C)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['309', '312'])).
% 54.39/54.62  thf('314', plain,
% 54.39/54.62      (((((sk_C) = (k1_xboole_0))
% 54.39/54.62         | (zip_tseitin_0 @ sk_C @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_B @ 
% 54.39/54.62            sk_A)))
% 54.39/54.62         <= (((r1_xboole_0 @ sk_B @ sk_C)) & 
% 54.39/54.62             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 54.39/54.62             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('sup-', [status(thm)], ['308', '313'])).
% 54.39/54.62  thf('315', plain,
% 54.39/54.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 54.39/54.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.62      inference('split', [status(esa)], ['230'])).
% 54.39/54.62  thf('316', plain,
% 54.39/54.62      (((v1_tops_1 @ sk_B @ sk_A)) <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 54.39/54.62      inference('split', [status(esa)], ['0'])).
% 54.39/54.62  thf('317', plain,
% 54.39/54.62      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 54.39/54.62        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 54.39/54.62      inference('demod', [status(thm)], ['62', '63'])).
% 54.39/54.62  thf('318', plain,
% 54.39/54.62      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 54.39/54.62         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 54.39/54.62      inference('sup-', [status(thm)], ['316', '317'])).
% 54.39/54.62  thf('319', plain,
% 54.39/54.62      (![X37 : $i]:
% 54.39/54.62         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 54.39/54.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.39/54.62  thf('320', plain,
% 54.39/54.62      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 54.39/54.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.63          | ((X33) != (k2_pre_topc @ X32 @ X31))
% 54.39/54.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.63          | ~ (zip_tseitin_0 @ X34 @ X35 @ X31 @ X32)
% 54.39/54.63          | ~ (r2_hidden @ X35 @ X33)
% 54.39/54.63          | ~ (r2_hidden @ X35 @ (u1_struct_0 @ X32))
% 54.39/54.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.63          | ~ (l1_pre_topc @ X32))),
% 54.39/54.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 54.39/54.63  thf('321', plain,
% 54.39/54.63      (![X31 : $i, X32 : $i, X34 : $i, X35 : $i]:
% 54.39/54.63         (~ (l1_pre_topc @ X32)
% 54.39/54.63          | ~ (m1_subset_1 @ (k2_pre_topc @ X32 @ X31) @ 
% 54.39/54.63               (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.63          | ~ (r2_hidden @ X35 @ (u1_struct_0 @ X32))
% 54.39/54.63          | ~ (r2_hidden @ X35 @ (k2_pre_topc @ X32 @ X31))
% 54.39/54.63          | ~ (zip_tseitin_0 @ X34 @ X35 @ X31 @ X32)
% 54.39/54.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 54.39/54.63          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 54.39/54.63      inference('simplify', [status(thm)], ['320'])).
% 54.39/54.63  thf('322', plain,
% 54.39/54.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 54.39/54.63         (~ (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 54.39/54.63             (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 54.39/54.63          | ~ (l1_struct_0 @ X0)
% 54.39/54.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.39/54.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.39/54.63          | ~ (zip_tseitin_0 @ X2 @ X3 @ X1 @ X0)
% 54.39/54.63          | ~ (r2_hidden @ X3 @ (k2_pre_topc @ X0 @ X1))
% 54.39/54.63          | ~ (r2_hidden @ X3 @ (u1_struct_0 @ X0))
% 54.39/54.63          | ~ (l1_pre_topc @ X0))),
% 54.39/54.63      inference('sup-', [status(thm)], ['319', '321'])).
% 54.39/54.63  thf('323', plain,
% 54.39/54.63      ((![X0 : $i, X1 : $i]:
% 54.39/54.63          (~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 54.39/54.63              (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 54.39/54.63           | ~ (l1_pre_topc @ sk_A)
% 54.39/54.63           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 54.39/54.63           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 54.39/54.63           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 54.39/54.63           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.63           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.39/54.63           | ~ (l1_struct_0 @ sk_A)))
% 54.39/54.63         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 54.39/54.63      inference('sup-', [status(thm)], ['318', '322'])).
% 54.39/54.63  thf('324', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 54.39/54.63      inference('demod', [status(thm)], ['2', '3'])).
% 54.39/54.63  thf('325', plain, ((l1_pre_topc @ sk_A)),
% 54.39/54.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.63  thf('326', plain,
% 54.39/54.63      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 54.39/54.63         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 54.39/54.63      inference('sup-', [status(thm)], ['316', '317'])).
% 54.39/54.63  thf('327', plain,
% 54.39/54.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.39/54.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.39/54.63  thf('328', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.63      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.63  thf('329', plain,
% 54.39/54.63      ((![X0 : $i, X1 : $i]:
% 54.39/54.63          (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 54.39/54.63           | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 54.39/54.63           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 54.39/54.63           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 54.39/54.63         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 54.39/54.63      inference('demod', [status(thm)],
% 54.39/54.63                ['323', '324', '325', '326', '327', '328'])).
% 54.39/54.63  thf('330', plain,
% 54.39/54.63      ((![X0 : $i]:
% 54.39/54.63          (~ (zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A)
% 54.39/54.63           | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 54.39/54.63           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))))
% 54.39/54.63         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 54.39/54.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('sup-', [status(thm)], ['315', '329'])).
% 54.39/54.63  thf('331', plain,
% 54.39/54.63      (((((sk_C) = (k1_xboole_0))
% 54.39/54.63         | ~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 54.39/54.63              (u1_struct_0 @ sk_A))
% 54.39/54.63         | ~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 54.39/54.63              (k2_struct_0 @ sk_A))))
% 54.39/54.63         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 54.39/54.63             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 54.39/54.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 54.39/54.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('sup-', [status(thm)], ['314', '330'])).
% 54.39/54.63  thf('332', plain,
% 54.39/54.63      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.39/54.63         | ((sk_C) = (k1_xboole_0))))
% 54.39/54.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('demod', [status(thm)], ['236', '289'])).
% 54.39/54.63  thf('333', plain,
% 54.39/54.63      (((~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 54.39/54.63            (k2_struct_0 @ sk_A))
% 54.39/54.63         | ((sk_C) = (k1_xboole_0))))
% 54.39/54.63         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 54.39/54.63             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 54.39/54.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 54.39/54.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('clc', [status(thm)], ['331', '332'])).
% 54.39/54.63  thf('334', plain,
% 54.39/54.63      (![X37 : $i]:
% 54.39/54.63         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 54.39/54.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.39/54.63  thf('335', plain,
% 54.39/54.63      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.39/54.63         | ((sk_C) = (k1_xboole_0))))
% 54.39/54.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('demod', [status(thm)], ['236', '289'])).
% 54.39/54.63  thf('336', plain,
% 54.39/54.63      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 54.39/54.63         | ~ (l1_struct_0 @ sk_A)
% 54.39/54.63         | ((sk_C) = (k1_xboole_0))))
% 54.39/54.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('sup+', [status(thm)], ['334', '335'])).
% 54.39/54.63  thf('337', plain, ((l1_struct_0 @ sk_A)),
% 54.39/54.63      inference('sup-', [status(thm)], ['55', '56'])).
% 54.39/54.63  thf('338', plain,
% 54.39/54.63      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 54.39/54.63         | ((sk_C) = (k1_xboole_0))))
% 54.39/54.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('demod', [status(thm)], ['336', '337'])).
% 54.39/54.63  thf('339', plain,
% 54.39/54.63      ((((sk_C) = (k1_xboole_0)))
% 54.39/54.63         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 54.39/54.63             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 54.39/54.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 54.39/54.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('clc', [status(thm)], ['333', '338'])).
% 54.39/54.63  thf('340', plain,
% 54.39/54.63      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 54.39/54.63      inference('split', [status(esa)], ['228'])).
% 54.39/54.63  thf('341', plain,
% 54.39/54.63      ((((sk_C) != (sk_C)))
% 54.39/54.63         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 54.39/54.63             ((v1_tops_1 @ sk_B @ sk_A)) & 
% 54.39/54.63             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 54.39/54.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 54.39/54.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 54.39/54.63      inference('sup-', [status(thm)], ['339', '340'])).
% 54.39/54.63  thf('342', plain,
% 54.39/54.63      (~ ((v1_tops_1 @ sk_B @ sk_A)) | 
% 54.39/54.63       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 54.39/54.63       ~ ((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 54.39/54.63       (((sk_C) = (k1_xboole_0)))),
% 54.39/54.63      inference('simplify', [status(thm)], ['341'])).
% 54.39/54.63  thf('343', plain, ($false),
% 54.39/54.63      inference('sat_resolution*', [status(thm)],
% 54.39/54.63                ['1', '224', '225', '227', '229', '231', '342'])).
% 54.39/54.63  
% 54.39/54.63  % SZS output end Refutation
% 54.39/54.63  
% 54.39/54.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
