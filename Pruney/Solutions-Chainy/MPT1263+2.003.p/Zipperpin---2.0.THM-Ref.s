%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ALt6YYK3Si

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:06 EST 2020

% Result     : Theorem 51.69s
% Output     : Refutation 51.69s
% Verified   : 
% Statistics : Number of formulae       :  361 (2254 expanded)
%              Number of leaves         :   52 ( 700 expanded)
%              Depth                    :   33
%              Number of atoms          : 4061 (28554 expanded)
%              Number of equality atoms :  228 (1567 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X52: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X52 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X52 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_B @ X52 )
      | ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X34 @ X32 @ X33 ) @ X34 )
      | ( zip_tseitin_0 @ ( sk_E @ X34 @ X32 @ X33 ) @ ( sk_D @ X34 @ X32 @ X33 ) @ X32 @ X33 )
      | ( X34
        = ( k2_pre_topc @ X33 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r2_hidden @ ( sk_D @ X34 @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) )
      | ( X34
        = ( k2_pre_topc @ X33 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ X30 @ X27 )
      | ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X28 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X34 @ X32 @ X33 ) @ X34 )
      | ( m1_subset_1 @ ( sk_E @ X34 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( X34
        = ( k2_pre_topc @ X33 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
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
    ( ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,
    ( ( ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','17'])).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v3_pre_topc @ X27 @ X28 )
      | ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X28 ) ) ),
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
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(clc,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','17'])).

thf('40',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X27 )
      | ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('41',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v1_tops_1 @ X46 @ X47 )
      | ( ( k2_pre_topc @ X47 @ X46 )
        = ( k2_struct_0 @ X47 ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X49: $i] :
      ( ( ( k2_pre_topc @ X49 @ ( k2_struct_0 @ X49 ) )
        = ( k2_struct_0 @ X49 ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X38: $i] :
      ( ( ( k2_struct_0 @ X38 )
        = ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('50',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k2_pre_topc @ X47 @ X46 )
       != ( k2_struct_0 @ X47 ) )
      | ( v1_tops_1 @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('55',plain,(
    ! [X39: $i] :
      ( ( l1_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['46','56'])).

thf('58',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(clc,[status(thm)],['34','37'])).

thf('59',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('60',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X38: $i] :
      ( ( ( k2_struct_0 @ X38 )
        = ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k2_pre_topc @ X47 @ X46 )
       != ( k2_struct_0 @ X47 ) )
      | ( v1_tops_1 @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X39: $i] :
      ( ( l1_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v1_tops_1 @ X46 @ X47 )
      | ( ( k2_pre_topc @ X47 @ X46 )
        = ( k2_struct_0 @ X47 ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ sk_B )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup+',[status(thm)],['61','81'])).

thf('83',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('85',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) @ X51 )
      | ( v4_pre_topc @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('91',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('93',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('95',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','96'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('98',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('99',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('104',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','97','110'])).

thf('112',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup-',[status(thm)],['83','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('116',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v4_pre_topc @ X40 @ X41 )
      | ( ( k2_pre_topc @ X41 @ X40 )
        = X40 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference('sup+',[status(thm)],['57','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('126',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(demod,[status(thm)],['43','124','125'])).

thf('127',plain,(
    ! [X38: $i] :
      ( ( ( k2_struct_0 @ X38 )
        = ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    ! [X49: $i] :
      ( ( ( k2_pre_topc @ X49 @ ( k2_struct_0 @ X49 ) )
        = ( k2_struct_0 @ X49 ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('129',plain,(
    ! [X38: $i] :
      ( ( ( k2_struct_0 @ X38 )
        = ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('131',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v2_pre_topc @ X41 )
      | ( ( k2_pre_topc @ X41 @ X40 )
       != X40 )
      | ( v4_pre_topc @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('139',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v4_pre_topc @ X50 @ X51 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','96'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('148',plain,(
    ! [X48: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X48 ) @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('149',plain,(
    ! [X38: $i] :
      ( ( ( k2_struct_0 @ X38 )
        = ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('150',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('151',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) @ X51 )
      | ( v4_pre_topc @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['147','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','158'])).

thf('160',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('161',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('164',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('165',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v4_pre_topc @ X40 @ X41 )
      | ( ( k2_pre_topc @ X41 @ X40 )
        = X40 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( ( k2_pre_topc @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['162','167'])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('172',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
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

thf('173',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( r2_hidden @ X44 @ ( k2_pre_topc @ X43 @ X42 ) )
      | ~ ( r1_xboole_0 @ X42 @ X45 )
      | ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( v3_pre_topc @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X43 ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('176',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('177',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('180',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['174','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['170','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('190',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( m1_subset_1 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['188','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','192'])).

thf('194',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(clc,[status(thm)],['126','197'])).

thf('199',plain,(
    ! [X38: $i] :
      ( ( ( k2_struct_0 @ X38 )
        = ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('200',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('203',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['46','56'])).

thf('205',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X52: $i] :
        ( ( X52 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X52 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('206',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['206'])).

thf('208',plain,
    ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference('sup-',[status(thm)],['205','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','97','110'])).

thf('210',plain,
    ( ( ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('214',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference('sup+',[status(thm)],['204','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k2_pre_topc @ X47 @ X46 )
       != ( k2_struct_0 @ X47 ) )
      | ( v1_tops_1 @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('221',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference('sup-',[status(thm)],['203','223'])).

thf('225',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['206'])).

thf('226',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      & ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) ) ) ),
    inference('sup-',[status(thm)],['198','226'])).

thf('228',plain,
    ( ~ ! [X52: $i] :
          ( ( X52 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X52 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X52 ) )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['206'])).

thf('230',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['230'])).

thf('232',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['232'])).

thf('234',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['234'])).

thf('236',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['234'])).

thf('237',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('238',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r2_hidden @ ( sk_D @ X34 @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) )
      | ( X34
        = ( k2_pre_topc @ X33 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['236','239'])).

thf('241',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['168','169'])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','105'])).

thf('246',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v4_pre_topc @ X50 @ X51 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k5_xboole_0 @ X1 @ X1 ) ) @ X0 )
      | ~ ( v4_pre_topc @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['253','256'])).

thf('258',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['244','257'])).

thf('259',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['181'])).

thf('262',plain,(
    ! [X27: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X31 )
      | ~ ( r1_xboole_0 @ X30 @ X27 )
      | ~ ( r2_hidden @ X29 @ X27 )
      | ~ ( v3_pre_topc @ X27 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('263',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['260','263'])).

thf('265',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['243','264'])).

thf('266',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('267',plain,(
    ! [X32: $i,X33: $i,X34: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r2_hidden @ ( sk_D @ X34 @ X32 @ X33 ) @ X34 )
      | ~ ( zip_tseitin_0 @ X37 @ ( sk_D @ X34 @ X32 @ X33 ) @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( X34
        = ( k2_pre_topc @ X33 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('268',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['265','268'])).

thf('270',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('271',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['168','169'])).

thf('272',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['234'])).

thf('273',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['269','270','271','272','273'])).

thf('275',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('277',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('278',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['230'])).

thf('280',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['206'])).

thf('281',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['234'])).

thf('282',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( r2_hidden @ X44 @ ( k2_pre_topc @ X43 @ X42 ) )
      | ~ ( r1_xboole_0 @ X42 @ X45 )
      | ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( v3_pre_topc @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X43 ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('284',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['284','285'])).

thf('287',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( r1_xboole_0 @ sk_B @ sk_C )
        | ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( v3_pre_topc @ sk_C @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['281','286'])).

thf('288',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v3_pre_topc @ sk_C @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['280','287'])).

thf('289',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['279','288'])).

thf('290',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['234'])).

thf('291',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( m1_subset_1 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('292',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['289','292'])).

thf('294',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['278','293'])).

thf('295',plain,(
    ! [X38: $i] :
      ( ( ( k2_struct_0 @ X38 )
        = ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('296',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['234'])).

thf('297',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['295','296'])).

thf('298',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('299',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['297','298'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('300',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('301',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['294','301'])).

thf('303',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['275','302'])).

thf('304',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['232'])).

thf('305',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['305'])).

thf('307',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','228','229','231','233','235','306'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ALt6YYK3Si
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 51.69/51.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 51.69/51.88  % Solved by: fo/fo7.sh
% 51.69/51.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.69/51.88  % done 66585 iterations in 51.415s
% 51.69/51.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 51.69/51.88  % SZS output start Refutation
% 51.69/51.88  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 51.69/51.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 51.69/51.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 51.69/51.88  thf(sk_B_type, type, sk_B: $i).
% 51.69/51.88  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 51.69/51.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.69/51.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 51.69/51.88  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 51.69/51.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 51.69/51.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 51.69/51.88  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 51.69/51.88  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 51.69/51.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 51.69/51.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 51.69/51.88  thf(sk_C_type, type, sk_C: $i).
% 51.69/51.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 51.69/51.88  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 51.69/51.88  thf(sk_A_type, type, sk_A: $i).
% 51.69/51.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 51.69/51.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 51.69/51.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 51.69/51.88  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 51.69/51.88  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 51.69/51.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 51.69/51.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 51.69/51.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.69/51.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 51.69/51.88  thf(t80_tops_1, conjecture,
% 51.69/51.88    (![A:$i]:
% 51.69/51.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 51.69/51.88       ( ![B:$i]:
% 51.69/51.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88           ( ( v1_tops_1 @ B @ A ) <=>
% 51.69/51.88             ( ![C:$i]:
% 51.69/51.88               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88                 ( ~( ( ( C ) != ( k1_xboole_0 ) ) & ( v3_pre_topc @ C @ A ) & 
% 51.69/51.88                      ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ))).
% 51.69/51.88  thf(zf_stmt_0, negated_conjecture,
% 51.69/51.88    (~( ![A:$i]:
% 51.69/51.88        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 51.69/51.88          ( ![B:$i]:
% 51.69/51.88            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88              ( ( v1_tops_1 @ B @ A ) <=>
% 51.69/51.88                ( ![C:$i]:
% 51.69/51.88                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88                    ( ~( ( ( C ) != ( k1_xboole_0 ) ) & 
% 51.69/51.88                         ( v3_pre_topc @ C @ A ) & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ) )),
% 51.69/51.88    inference('cnf.neg', [status(esa)], [t80_tops_1])).
% 51.69/51.88  thf('0', plain,
% 51.69/51.88      (![X52 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ((X52) = (k1_xboole_0))
% 51.69/51.88          | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88          | ~ (r1_xboole_0 @ sk_B @ X52)
% 51.69/51.88          | (v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('1', plain,
% 51.69/51.88      ((![X52 : $i]:
% 51.69/51.88          (((X52) = (k1_xboole_0))
% 51.69/51.88           | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88           | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88           | ~ (r1_xboole_0 @ sk_B @ X52))) | 
% 51.69/51.88       ((v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.88      inference('split', [status(esa)], ['0'])).
% 51.69/51.88  thf(dt_k2_subset_1, axiom,
% 51.69/51.88    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 51.69/51.88  thf('2', plain,
% 51.69/51.88      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 51.69/51.88      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 51.69/51.88  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 51.69/51.88  thf('3', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 51.69/51.88      inference('cnf', [status(esa)], [d4_subset_1])).
% 51.69/51.88  thf('4', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.88      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.88  thf('5', plain,
% 51.69/51.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf(d13_pre_topc, axiom,
% 51.69/51.88    (![A:$i]:
% 51.69/51.88     ( ( l1_pre_topc @ A ) =>
% 51.69/51.88       ( ![B:$i]:
% 51.69/51.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88           ( ![C:$i]:
% 51.69/51.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 51.69/51.88                 ( ![D:$i]:
% 51.69/51.88                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 51.69/51.88                     ( ( r2_hidden @ D @ C ) <=>
% 51.69/51.88                       ( ![E:$i]:
% 51.69/51.88                         ( ( m1_subset_1 @
% 51.69/51.88                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88                           ( ~( ( r1_xboole_0 @ B @ E ) & 
% 51.69/51.88                                ( r2_hidden @ D @ E ) & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 51.69/51.88  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 51.69/51.88  thf(zf_stmt_2, axiom,
% 51.69/51.88    (![E:$i,D:$i,B:$i,A:$i]:
% 51.69/51.88     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 51.69/51.88       ( ( v3_pre_topc @ E @ A ) & ( r2_hidden @ D @ E ) & 
% 51.69/51.88         ( r1_xboole_0 @ B @ E ) ) ))).
% 51.69/51.88  thf(zf_stmt_3, axiom,
% 51.69/51.88    (![A:$i]:
% 51.69/51.88     ( ( l1_pre_topc @ A ) =>
% 51.69/51.88       ( ![B:$i]:
% 51.69/51.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88           ( ![C:$i]:
% 51.69/51.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 51.69/51.88                 ( ![D:$i]:
% 51.69/51.88                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 51.69/51.88                     ( ( r2_hidden @ D @ C ) <=>
% 51.69/51.88                       ( ![E:$i]:
% 51.69/51.88                         ( ( m1_subset_1 @
% 51.69/51.88                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88                           ( ~( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 51.69/51.88  thf('6', plain,
% 51.69/51.88      (![X32 : $i, X33 : $i, X34 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.88          | ~ (r2_hidden @ (sk_D @ X34 @ X32 @ X33) @ X34)
% 51.69/51.88          | (zip_tseitin_0 @ (sk_E @ X34 @ X32 @ X33) @ 
% 51.69/51.88             (sk_D @ X34 @ X32 @ X33) @ X32 @ X33)
% 51.69/51.88          | ((X34) = (k2_pre_topc @ X33 @ X32))
% 51.69/51.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.88          | ~ (l1_pre_topc @ X33))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 51.69/51.88  thf('7', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (l1_pre_topc @ sk_A)
% 51.69/51.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 51.69/51.88             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 51.69/51.88          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 51.69/51.88      inference('sup-', [status(thm)], ['5', '6'])).
% 51.69/51.88  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('9', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 51.69/51.88             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 51.69/51.88          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 51.69/51.88      inference('demod', [status(thm)], ['7', '8'])).
% 51.69/51.88  thf('10', plain,
% 51.69/51.88      ((~ (r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88           (u1_struct_0 @ sk_A))
% 51.69/51.88        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 51.69/51.88        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 51.69/51.88      inference('sup-', [status(thm)], ['4', '9'])).
% 51.69/51.88  thf('11', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.88      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.88  thf('12', plain,
% 51.69/51.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('13', plain,
% 51.69/51.88      (![X32 : $i, X33 : $i, X34 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.88          | (r2_hidden @ (sk_D @ X34 @ X32 @ X33) @ (u1_struct_0 @ X33))
% 51.69/51.88          | ((X34) = (k2_pre_topc @ X33 @ X32))
% 51.69/51.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.88          | ~ (l1_pre_topc @ X33))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 51.69/51.88  thf('14', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (l1_pre_topc @ sk_A)
% 51.69/51.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 51.69/51.88      inference('sup-', [status(thm)], ['12', '13'])).
% 51.69/51.88  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('16', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 51.69/51.88      inference('demod', [status(thm)], ['14', '15'])).
% 51.69/51.88  thf('17', plain,
% 51.69/51.88      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88         (u1_struct_0 @ sk_A))
% 51.69/51.88        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 51.69/51.88      inference('sup-', [status(thm)], ['11', '16'])).
% 51.69/51.88  thf('18', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 51.69/51.88      inference('clc', [status(thm)], ['10', '17'])).
% 51.69/51.88  thf('19', plain,
% 51.69/51.88      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 51.69/51.88         ((r1_xboole_0 @ X30 @ X27) | ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X28))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 51.69/51.88  thf('20', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A)))),
% 51.69/51.88      inference('sup-', [status(thm)], ['18', '19'])).
% 51.69/51.88  thf('21', plain,
% 51.69/51.88      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88         (u1_struct_0 @ sk_A))
% 51.69/51.88        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 51.69/51.88      inference('sup-', [status(thm)], ['11', '16'])).
% 51.69/51.88  thf('22', plain,
% 51.69/51.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('23', plain,
% 51.69/51.88      (![X32 : $i, X33 : $i, X34 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.88          | ~ (r2_hidden @ (sk_D @ X34 @ X32 @ X33) @ X34)
% 51.69/51.88          | (m1_subset_1 @ (sk_E @ X34 @ X32 @ X33) @ 
% 51.69/51.88             (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.88          | ((X34) = (k2_pre_topc @ X33 @ X32))
% 51.69/51.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.88          | ~ (l1_pre_topc @ X33))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 51.69/51.88  thf('24', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (l1_pre_topc @ sk_A)
% 51.69/51.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 51.69/51.88             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 51.69/51.88      inference('sup-', [status(thm)], ['22', '23'])).
% 51.69/51.88  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('26', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 51.69/51.88             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 51.69/51.88      inference('demod', [status(thm)], ['24', '25'])).
% 51.69/51.88  thf('27', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.69/51.88             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 51.69/51.88      inference('sup-', [status(thm)], ['21', '26'])).
% 51.69/51.88  thf('28', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.88      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.88  thf('29', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 51.69/51.88      inference('demod', [status(thm)], ['27', '28'])).
% 51.69/51.88  thf('30', plain,
% 51.69/51.88      (((m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 51.69/51.88      inference('simplify', [status(thm)], ['29'])).
% 51.69/51.88  thf('31', plain,
% 51.69/51.88      ((![X52 : $i]:
% 51.69/51.88          (((X52) = (k1_xboole_0))
% 51.69/51.88           | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88           | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88           | ~ (r1_xboole_0 @ sk_B @ X52)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('split', [status(esa)], ['0'])).
% 51.69/51.88  thf('32', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | ~ (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A))
% 51.69/51.88         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 51.69/51.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('sup-', [status(thm)], ['30', '31'])).
% 51.69/51.88  thf('33', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 51.69/51.88         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 51.69/51.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('sup-', [status(thm)], ['20', '32'])).
% 51.69/51.88  thf('34', plain,
% 51.69/51.88      (((~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 51.69/51.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 51.69/51.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('simplify', [status(thm)], ['33'])).
% 51.69/51.88  thf('35', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 51.69/51.88      inference('clc', [status(thm)], ['10', '17'])).
% 51.69/51.88  thf('36', plain,
% 51.69/51.88      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 51.69/51.88         ((v3_pre_topc @ X27 @ X28) | ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X28))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 51.69/51.88  thf('37', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 51.69/51.88      inference('sup-', [status(thm)], ['35', '36'])).
% 51.69/51.88  thf('38', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('clc', [status(thm)], ['34', '37'])).
% 51.69/51.88  thf('39', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 51.69/51.88      inference('clc', [status(thm)], ['10', '17'])).
% 51.69/51.88  thf('40', plain,
% 51.69/51.88      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 51.69/51.88         ((r2_hidden @ X29 @ X27) | ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X28))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 51.69/51.88  thf('41', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88           (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A)))),
% 51.69/51.88      inference('sup-', [status(thm)], ['39', '40'])).
% 51.69/51.88  thf('42', plain,
% 51.69/51.88      ((((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ k1_xboole_0)
% 51.69/51.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('sup+', [status(thm)], ['38', '41'])).
% 51.69/51.88  thf('43', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | (r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.88            k1_xboole_0)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('simplify', [status(thm)], ['42'])).
% 51.69/51.88  thf('44', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.88      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.88  thf(d3_tops_1, axiom,
% 51.69/51.88    (![A:$i]:
% 51.69/51.88     ( ( l1_pre_topc @ A ) =>
% 51.69/51.88       ( ![B:$i]:
% 51.69/51.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88           ( ( v1_tops_1 @ B @ A ) <=>
% 51.69/51.88             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 51.69/51.88  thf('45', plain,
% 51.69/51.88      (![X46 : $i, X47 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 51.69/51.88          | ~ (v1_tops_1 @ X46 @ X47)
% 51.69/51.88          | ((k2_pre_topc @ X47 @ X46) = (k2_struct_0 @ X47))
% 51.69/51.88          | ~ (l1_pre_topc @ X47))),
% 51.69/51.88      inference('cnf', [status(esa)], [d3_tops_1])).
% 51.69/51.88  thf('46', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (l1_pre_topc @ X0)
% 51.69/51.88          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 51.69/51.88          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 51.69/51.88      inference('sup-', [status(thm)], ['44', '45'])).
% 51.69/51.88  thf(t27_tops_1, axiom,
% 51.69/51.88    (![A:$i]:
% 51.69/51.88     ( ( l1_pre_topc @ A ) =>
% 51.69/51.88       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 51.69/51.88  thf('47', plain,
% 51.69/51.88      (![X49 : $i]:
% 51.69/51.88         (((k2_pre_topc @ X49 @ (k2_struct_0 @ X49)) = (k2_struct_0 @ X49))
% 51.69/51.88          | ~ (l1_pre_topc @ X49))),
% 51.69/51.88      inference('cnf', [status(esa)], [t27_tops_1])).
% 51.69/51.88  thf(d3_struct_0, axiom,
% 51.69/51.88    (![A:$i]:
% 51.69/51.88     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 51.69/51.88  thf('48', plain,
% 51.69/51.88      (![X38 : $i]:
% 51.69/51.88         (((k2_struct_0 @ X38) = (u1_struct_0 @ X38)) | ~ (l1_struct_0 @ X38))),
% 51.69/51.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.69/51.88  thf('49', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.88      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.88  thf('50', plain,
% 51.69/51.88      (![X46 : $i, X47 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 51.69/51.88          | ((k2_pre_topc @ X47 @ X46) != (k2_struct_0 @ X47))
% 51.69/51.88          | (v1_tops_1 @ X46 @ X47)
% 51.69/51.88          | ~ (l1_pre_topc @ X47))),
% 51.69/51.88      inference('cnf', [status(esa)], [d3_tops_1])).
% 51.69/51.88  thf('51', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (l1_pre_topc @ X0)
% 51.69/51.88          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.88          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 51.69/51.88      inference('sup-', [status(thm)], ['49', '50'])).
% 51.69/51.88  thf('52', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (k2_struct_0 @ X0))
% 51.69/51.88          | ~ (l1_struct_0 @ X0)
% 51.69/51.88          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.88          | ~ (l1_pre_topc @ X0))),
% 51.69/51.88      inference('sup-', [status(thm)], ['48', '51'])).
% 51.69/51.88  thf('53', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 51.69/51.88          | ~ (l1_pre_topc @ X0)
% 51.69/51.88          | ~ (l1_pre_topc @ X0)
% 51.69/51.88          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.88          | ~ (l1_struct_0 @ X0))),
% 51.69/51.88      inference('sup-', [status(thm)], ['47', '52'])).
% 51.69/51.88  thf('54', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (l1_struct_0 @ X0)
% 51.69/51.88          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.88          | ~ (l1_pre_topc @ X0))),
% 51.69/51.88      inference('simplify', [status(thm)], ['53'])).
% 51.69/51.88  thf(dt_l1_pre_topc, axiom,
% 51.69/51.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 51.69/51.88  thf('55', plain,
% 51.69/51.88      (![X39 : $i]: ((l1_struct_0 @ X39) | ~ (l1_pre_topc @ X39))),
% 51.69/51.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 51.69/51.88  thf('56', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 51.69/51.88      inference('clc', [status(thm)], ['54', '55'])).
% 51.69/51.88  thf('57', plain,
% 51.69/51.88      (![X0 : $i]:
% 51.69/51.88         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 51.69/51.88          | ~ (l1_pre_topc @ X0))),
% 51.69/51.88      inference('clc', [status(thm)], ['46', '56'])).
% 51.69/51.88  thf('58', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('clc', [status(thm)], ['34', '37'])).
% 51.69/51.88  thf('59', plain,
% 51.69/51.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88        | (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 51.69/51.88      inference('sup-', [status(thm)], ['35', '36'])).
% 51.69/51.88  thf('60', plain,
% 51.69/51.88      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 51.69/51.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('sup+', [status(thm)], ['58', '59'])).
% 51.69/51.88  thf('61', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('simplify', [status(thm)], ['60'])).
% 51.69/51.88  thf('62', plain,
% 51.69/51.88      (![X38 : $i]:
% 51.69/51.88         (((k2_struct_0 @ X38) = (u1_struct_0 @ X38)) | ~ (l1_struct_0 @ X38))),
% 51.69/51.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.69/51.88  thf('63', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.88         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('simplify', [status(thm)], ['60'])).
% 51.69/51.88  thf('64', plain,
% 51.69/51.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('65', plain,
% 51.69/51.88      (![X46 : $i, X47 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 51.69/51.88          | ((k2_pre_topc @ X47 @ X46) != (k2_struct_0 @ X47))
% 51.69/51.88          | (v1_tops_1 @ X46 @ X47)
% 51.69/51.88          | ~ (l1_pre_topc @ X47))),
% 51.69/51.88      inference('cnf', [status(esa)], [d3_tops_1])).
% 51.69/51.88  thf('66', plain,
% 51.69/51.88      ((~ (l1_pre_topc @ sk_A)
% 51.69/51.88        | (v1_tops_1 @ sk_B @ sk_A)
% 51.69/51.88        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 51.69/51.88      inference('sup-', [status(thm)], ['64', '65'])).
% 51.69/51.88  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('68', plain,
% 51.69/51.88      (((v1_tops_1 @ sk_B @ sk_A)
% 51.69/51.88        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 51.69/51.88      inference('demod', [status(thm)], ['66', '67'])).
% 51.69/51.88  thf('69', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 51.69/51.88         | (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 51.69/51.88         | (v1_tops_1 @ sk_B @ sk_A)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('sup-', [status(thm)], ['63', '68'])).
% 51.69/51.88  thf('70', plain,
% 51.69/51.88      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 51.69/51.88         | ~ (l1_struct_0 @ sk_A)
% 51.69/51.88         | (v1_tops_1 @ sk_B @ sk_A)
% 51.69/51.88         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('sup-', [status(thm)], ['62', '69'])).
% 51.69/51.88  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('72', plain,
% 51.69/51.88      (![X39 : $i]: ((l1_struct_0 @ X39) | ~ (l1_pre_topc @ X39))),
% 51.69/51.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 51.69/51.88  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 51.69/51.88      inference('sup-', [status(thm)], ['71', '72'])).
% 51.69/51.88  thf('74', plain,
% 51.69/51.88      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 51.69/51.88         | (v1_tops_1 @ sk_B @ sk_A)
% 51.69/51.88         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('demod', [status(thm)], ['70', '73'])).
% 51.69/51.88  thf('75', plain,
% 51.69/51.88      ((((v3_pre_topc @ k1_xboole_0 @ sk_A) | (v1_tops_1 @ sk_B @ sk_A)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('simplify', [status(thm)], ['74'])).
% 51.69/51.88  thf('76', plain,
% 51.69/51.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('77', plain,
% 51.69/51.88      (![X46 : $i, X47 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 51.69/51.88          | ~ (v1_tops_1 @ X46 @ X47)
% 51.69/51.88          | ((k2_pre_topc @ X47 @ X46) = (k2_struct_0 @ X47))
% 51.69/51.88          | ~ (l1_pre_topc @ X47))),
% 51.69/51.88      inference('cnf', [status(esa)], [d3_tops_1])).
% 51.69/51.88  thf('78', plain,
% 51.69/51.88      ((~ (l1_pre_topc @ sk_A)
% 51.69/51.88        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 51.69/51.88        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.88      inference('sup-', [status(thm)], ['76', '77'])).
% 51.69/51.88  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.88  thf('80', plain,
% 51.69/51.88      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 51.69/51.88        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.88      inference('demod', [status(thm)], ['78', '79'])).
% 51.69/51.88  thf('81', plain,
% 51.69/51.88      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 51.69/51.88         | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('sup-', [status(thm)], ['75', '80'])).
% 51.69/51.88  thf('82', plain,
% 51.69/51.88      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 51.69/51.88         | (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 51.69/51.88         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('sup+', [status(thm)], ['61', '81'])).
% 51.69/51.88  thf('83', plain,
% 51.69/51.88      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 51.69/51.88         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 51.69/51.88         <= ((![X52 : $i]:
% 51.69/51.88                (((X52) = (k1_xboole_0))
% 51.69/51.88                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.88                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.88                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.88      inference('simplify', [status(thm)], ['82'])).
% 51.69/51.88  thf('84', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.88      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.88  thf(t29_tops_1, axiom,
% 51.69/51.88    (![A:$i]:
% 51.69/51.88     ( ( l1_pre_topc @ A ) =>
% 51.69/51.88       ( ![B:$i]:
% 51.69/51.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.88           ( ( v4_pre_topc @ B @ A ) <=>
% 51.69/51.88             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 51.69/51.88  thf('85', plain,
% 51.69/51.88      (![X50 : $i, X51 : $i]:
% 51.69/51.88         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 51.69/51.89          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50) @ X51)
% 51.69/51.89          | (v4_pre_topc @ X50 @ X51)
% 51.69/51.89          | ~ (l1_pre_topc @ X51))),
% 51.69/51.89      inference('cnf', [status(esa)], [t29_tops_1])).
% 51.69/51.89  thf('86', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (v3_pre_topc @ 
% 51.69/51.89               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['84', '85'])).
% 51.69/51.89  thf('87', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.89      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.89  thf(d5_subset_1, axiom,
% 51.69/51.89    (![A:$i,B:$i]:
% 51.69/51.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.69/51.89       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 51.69/51.89  thf('88', plain,
% 51.69/51.89      (![X10 : $i, X11 : $i]:
% 51.69/51.89         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 51.69/51.89          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 51.69/51.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.69/51.89  thf('89', plain,
% 51.69/51.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['87', '88'])).
% 51.69/51.89  thf('90', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.89      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.89  thf(t3_subset, axiom,
% 51.69/51.89    (![A:$i,B:$i]:
% 51.69/51.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 51.69/51.89  thf('91', plain,
% 51.69/51.89      (![X21 : $i, X22 : $i]:
% 51.69/51.89         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 51.69/51.89      inference('cnf', [status(esa)], [t3_subset])).
% 51.69/51.89  thf('92', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 51.69/51.89      inference('sup-', [status(thm)], ['90', '91'])).
% 51.69/51.89  thf(t28_xboole_1, axiom,
% 51.69/51.89    (![A:$i,B:$i]:
% 51.69/51.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 51.69/51.89  thf('93', plain,
% 51.69/51.89      (![X5 : $i, X6 : $i]:
% 51.69/51.89         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 51.69/51.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 51.69/51.89  thf('94', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['92', '93'])).
% 51.69/51.89  thf(t100_xboole_1, axiom,
% 51.69/51.89    (![A:$i,B:$i]:
% 51.69/51.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 51.69/51.89  thf('95', plain,
% 51.69/51.89      (![X3 : $i, X4 : $i]:
% 51.69/51.89         ((k4_xboole_0 @ X3 @ X4)
% 51.69/51.89           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 51.69/51.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 51.69/51.89  thf('96', plain,
% 51.69/51.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 51.69/51.89      inference('sup+', [status(thm)], ['94', '95'])).
% 51.69/51.89  thf('97', plain,
% 51.69/51.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['89', '96'])).
% 51.69/51.89  thf(t4_subset_1, axiom,
% 51.69/51.89    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 51.69/51.89  thf('98', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf(involutiveness_k3_subset_1, axiom,
% 51.69/51.89    (![A:$i,B:$i]:
% 51.69/51.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.69/51.89       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 51.69/51.89  thf('99', plain,
% 51.69/51.89      (![X13 : $i, X14 : $i]:
% 51.69/51.89         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 51.69/51.89          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 51.69/51.89      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.69/51.89  thf('100', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['98', '99'])).
% 51.69/51.89  thf('101', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf('102', plain,
% 51.69/51.89      (![X10 : $i, X11 : $i]:
% 51.69/51.89         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 51.69/51.89          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 51.69/51.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.69/51.89  thf('103', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['101', '102'])).
% 51.69/51.89  thf(t3_boole, axiom,
% 51.69/51.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 51.69/51.89  thf('104', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 51.69/51.89      inference('cnf', [status(esa)], [t3_boole])).
% 51.69/51.89  thf('105', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['103', '104'])).
% 51.69/51.89  thf('106', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['100', '105'])).
% 51.69/51.89  thf('107', plain,
% 51.69/51.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['87', '88'])).
% 51.69/51.89  thf('108', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['106', '107'])).
% 51.69/51.89  thf('109', plain,
% 51.69/51.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 51.69/51.89      inference('sup+', [status(thm)], ['94', '95'])).
% 51.69/51.89  thf('110', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['108', '109'])).
% 51.69/51.89  thf('111', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['86', '97', '110'])).
% 51.69/51.89  thf('112', plain,
% 51.69/51.89      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 51.69/51.89         | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 51.69/51.89         | ~ (l1_pre_topc @ sk_A)))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['83', '111'])).
% 51.69/51.89  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('114', plain,
% 51.69/51.89      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 51.69/51.89         | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('demod', [status(thm)], ['112', '113'])).
% 51.69/51.89  thf('115', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.89      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.89  thf(t52_pre_topc, axiom,
% 51.69/51.89    (![A:$i]:
% 51.69/51.89     ( ( l1_pre_topc @ A ) =>
% 51.69/51.89       ( ![B:$i]:
% 51.69/51.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.89           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 51.69/51.89             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 51.69/51.89               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 51.69/51.89  thf('116', plain,
% 51.69/51.89      (![X40 : $i, X41 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 51.69/51.89          | ~ (v4_pre_topc @ X40 @ X41)
% 51.69/51.89          | ((k2_pre_topc @ X41 @ X40) = (X40))
% 51.69/51.89          | ~ (l1_pre_topc @ X41))),
% 51.69/51.89      inference('cnf', [status(esa)], [t52_pre_topc])).
% 51.69/51.89  thf('117', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 51.69/51.89          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['115', '116'])).
% 51.69/51.89  thf('118', plain,
% 51.69/51.89      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 51.69/51.89         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 51.69/51.89         | ~ (l1_pre_topc @ sk_A)))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['114', '117'])).
% 51.69/51.89  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('120', plain,
% 51.69/51.89      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 51.69/51.89         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('demod', [status(thm)], ['118', '119'])).
% 51.69/51.89  thf('121', plain,
% 51.69/51.89      (((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 51.69/51.89         | ~ (l1_pre_topc @ sk_A)
% 51.69/51.89         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup+', [status(thm)], ['57', '120'])).
% 51.69/51.89  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('123', plain,
% 51.69/51.89      (((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 51.69/51.89         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('demod', [status(thm)], ['121', '122'])).
% 51.69/51.89  thf('124', plain,
% 51.69/51.89      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('simplify', [status(thm)], ['123'])).
% 51.69/51.89  thf('125', plain,
% 51.69/51.89      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('simplify', [status(thm)], ['123'])).
% 51.69/51.89  thf('126', plain,
% 51.69/51.89      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.89         | (r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 51.69/51.89            k1_xboole_0)))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('demod', [status(thm)], ['43', '124', '125'])).
% 51.69/51.89  thf('127', plain,
% 51.69/51.89      (![X38 : $i]:
% 51.69/51.89         (((k2_struct_0 @ X38) = (u1_struct_0 @ X38)) | ~ (l1_struct_0 @ X38))),
% 51.69/51.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.69/51.89  thf('128', plain,
% 51.69/51.89      (![X49 : $i]:
% 51.69/51.89         (((k2_pre_topc @ X49 @ (k2_struct_0 @ X49)) = (k2_struct_0 @ X49))
% 51.69/51.89          | ~ (l1_pre_topc @ X49))),
% 51.69/51.89      inference('cnf', [status(esa)], [t27_tops_1])).
% 51.69/51.89  thf('129', plain,
% 51.69/51.89      (![X38 : $i]:
% 51.69/51.89         (((k2_struct_0 @ X38) = (u1_struct_0 @ X38)) | ~ (l1_struct_0 @ X38))),
% 51.69/51.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.69/51.89  thf('130', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.89      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.89  thf('131', plain,
% 51.69/51.89      (![X40 : $i, X41 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 51.69/51.89          | ~ (v2_pre_topc @ X41)
% 51.69/51.89          | ((k2_pre_topc @ X41 @ X40) != (X40))
% 51.69/51.89          | (v4_pre_topc @ X40 @ X41)
% 51.69/51.89          | ~ (l1_pre_topc @ X41))),
% 51.69/51.89      inference('cnf', [status(esa)], [t52_pre_topc])).
% 51.69/51.89  thf('132', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0))
% 51.69/51.89          | ~ (v2_pre_topc @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['130', '131'])).
% 51.69/51.89  thf('133', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (u1_struct_0 @ X0))
% 51.69/51.89          | ~ (l1_struct_0 @ X0)
% 51.69/51.89          | ~ (v2_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['129', '132'])).
% 51.69/51.89  thf('134', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (((k2_struct_0 @ X0) != (u1_struct_0 @ X0))
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (v2_pre_topc @ X0)
% 51.69/51.89          | ~ (l1_struct_0 @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['128', '133'])).
% 51.69/51.89  thf('135', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_struct_0 @ X0)
% 51.69/51.89          | ~ (v2_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | ((k2_struct_0 @ X0) != (u1_struct_0 @ X0)))),
% 51.69/51.89      inference('simplify', [status(thm)], ['134'])).
% 51.69/51.89  thf('136', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 51.69/51.89          | ~ (l1_struct_0 @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (v2_pre_topc @ X0)
% 51.69/51.89          | ~ (l1_struct_0 @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['127', '135'])).
% 51.69/51.89  thf('137', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (v2_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (l1_struct_0 @ X0))),
% 51.69/51.89      inference('simplify', [status(thm)], ['136'])).
% 51.69/51.89  thf('138', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.89      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.89  thf('139', plain,
% 51.69/51.89      (![X50 : $i, X51 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 51.69/51.89          | ~ (v4_pre_topc @ X50 @ X51)
% 51.69/51.89          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50) @ X51)
% 51.69/51.89          | ~ (l1_pre_topc @ X51))),
% 51.69/51.89      inference('cnf', [status(esa)], [t29_tops_1])).
% 51.69/51.89  thf('140', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v3_pre_topc @ 
% 51.69/51.89             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 51.69/51.89          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['138', '139'])).
% 51.69/51.89  thf('141', plain,
% 51.69/51.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['89', '96'])).
% 51.69/51.89  thf('142', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['108', '109'])).
% 51.69/51.89  thf('143', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v3_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['140', '141', '142'])).
% 51.69/51.89  thf('144', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_struct_0 @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (v2_pre_topc @ X0)
% 51.69/51.89          | (v3_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['137', '143'])).
% 51.69/51.89  thf('145', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (v2_pre_topc @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (l1_struct_0 @ X0))),
% 51.69/51.89      inference('simplify', [status(thm)], ['144'])).
% 51.69/51.89  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('147', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['108', '109'])).
% 51.69/51.89  thf(fc10_tops_1, axiom,
% 51.69/51.89    (![A:$i]:
% 51.69/51.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 51.69/51.89       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 51.69/51.89  thf('148', plain,
% 51.69/51.89      (![X48 : $i]:
% 51.69/51.89         ((v3_pre_topc @ (k2_struct_0 @ X48) @ X48)
% 51.69/51.89          | ~ (l1_pre_topc @ X48)
% 51.69/51.89          | ~ (v2_pre_topc @ X48))),
% 51.69/51.89      inference('cnf', [status(esa)], [fc10_tops_1])).
% 51.69/51.89  thf('149', plain,
% 51.69/51.89      (![X38 : $i]:
% 51.69/51.89         (((k2_struct_0 @ X38) = (u1_struct_0 @ X38)) | ~ (l1_struct_0 @ X38))),
% 51.69/51.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.69/51.89  thf('150', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf('151', plain,
% 51.69/51.89      (![X50 : $i, X51 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 51.69/51.89          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50) @ X51)
% 51.69/51.89          | (v4_pre_topc @ X50 @ X51)
% 51.69/51.89          | ~ (l1_pre_topc @ X51))),
% 51.69/51.89      inference('cnf', [status(esa)], [t29_tops_1])).
% 51.69/51.89  thf('152', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (v3_pre_topc @ 
% 51.69/51.89               (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['150', '151'])).
% 51.69/51.89  thf('153', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['103', '104'])).
% 51.69/51.89  thf('154', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['152', '153'])).
% 51.69/51.89  thf('155', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (l1_struct_0 @ X0)
% 51.69/51.89          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['149', '154'])).
% 51.69/51.89  thf('156', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (v2_pre_topc @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (l1_struct_0 @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['148', '155'])).
% 51.69/51.89  thf('157', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_struct_0 @ X0)
% 51.69/51.89          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (v2_pre_topc @ X0))),
% 51.69/51.89      inference('simplify', [status(thm)], ['156'])).
% 51.69/51.89  thf('158', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         ((v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 51.69/51.89          | ~ (v2_pre_topc @ X1)
% 51.69/51.89          | ~ (l1_pre_topc @ X1)
% 51.69/51.89          | ~ (l1_struct_0 @ X1))),
% 51.69/51.89      inference('sup+', [status(thm)], ['147', '157'])).
% 51.69/51.89  thf('159', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_struct_0 @ sk_A)
% 51.69/51.89          | ~ (v2_pre_topc @ sk_A)
% 51.69/51.89          | (v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ sk_A))),
% 51.69/51.89      inference('sup-', [status(thm)], ['146', '158'])).
% 51.69/51.89  thf('160', plain, ((l1_struct_0 @ sk_A)),
% 51.69/51.89      inference('sup-', [status(thm)], ['71', '72'])).
% 51.69/51.89  thf('161', plain, ((v2_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('162', plain,
% 51.69/51.89      (![X0 : $i]: (v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ sk_A)),
% 51.69/51.89      inference('demod', [status(thm)], ['159', '160', '161'])).
% 51.69/51.89  thf('163', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['108', '109'])).
% 51.69/51.89  thf('164', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf('165', plain,
% 51.69/51.89      (![X40 : $i, X41 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 51.69/51.89          | ~ (v4_pre_topc @ X40 @ X41)
% 51.69/51.89          | ((k2_pre_topc @ X41 @ X40) = (X40))
% 51.69/51.89          | ~ (l1_pre_topc @ X41))),
% 51.69/51.89      inference('cnf', [status(esa)], [t52_pre_topc])).
% 51.69/51.89  thf('166', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 51.69/51.89          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['164', '165'])).
% 51.69/51.89  thf('167', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (~ (v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 51.69/51.89          | ((k2_pre_topc @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 51.69/51.89          | ~ (l1_pre_topc @ X1))),
% 51.69/51.89      inference('sup-', [status(thm)], ['163', '166'])).
% 51.69/51.89  thf('168', plain,
% 51.69/51.89      ((~ (l1_pre_topc @ sk_A)
% 51.69/51.89        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 51.69/51.89      inference('sup-', [status(thm)], ['162', '167'])).
% 51.69/51.89  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('170', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['168', '169'])).
% 51.69/51.89  thf('171', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf('172', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf(t54_pre_topc, axiom,
% 51.69/51.89    (![A:$i]:
% 51.69/51.89     ( ( l1_pre_topc @ A ) =>
% 51.69/51.89       ( ![B:$i]:
% 51.69/51.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.89           ( ![C:$i]:
% 51.69/51.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 51.69/51.89               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 51.69/51.89                 ( ( ~( v2_struct_0 @ A ) ) & 
% 51.69/51.89                   ( ![D:$i]:
% 51.69/51.89                     ( ( m1_subset_1 @
% 51.69/51.89                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.69/51.89                       ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 51.69/51.89                            ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 51.69/51.89  thf('173', plain,
% 51.69/51.89      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 51.69/51.89          | ~ (r2_hidden @ X44 @ (k2_pre_topc @ X43 @ X42))
% 51.69/51.89          | ~ (r1_xboole_0 @ X42 @ X45)
% 51.69/51.89          | ~ (r2_hidden @ X44 @ X45)
% 51.69/51.89          | ~ (v3_pre_topc @ X45 @ X43)
% 51.69/51.89          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 51.69/51.89          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X43))
% 51.69/51.89          | ~ (l1_pre_topc @ X43))),
% 51.69/51.89      inference('cnf', [status(esa)], [t54_pre_topc])).
% 51.69/51.89  thf('174', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 51.69/51.89          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.69/51.89          | ~ (v3_pre_topc @ X2 @ X0)
% 51.69/51.89          | ~ (r2_hidden @ X1 @ X2)
% 51.69/51.89          | ~ (r1_xboole_0 @ k1_xboole_0 @ X2)
% 51.69/51.89          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 51.69/51.89      inference('sup-', [status(thm)], ['172', '173'])).
% 51.69/51.89  thf('175', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf('176', plain,
% 51.69/51.89      (![X21 : $i, X22 : $i]:
% 51.69/51.89         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 51.69/51.89      inference('cnf', [status(esa)], [t3_subset])).
% 51.69/51.89  thf('177', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 51.69/51.89      inference('sup-', [status(thm)], ['175', '176'])).
% 51.69/51.89  thf('178', plain,
% 51.69/51.89      (![X5 : $i, X6 : $i]:
% 51.69/51.89         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 51.69/51.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 51.69/51.89  thf('179', plain,
% 51.69/51.89      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['177', '178'])).
% 51.69/51.89  thf(d7_xboole_0, axiom,
% 51.69/51.89    (![A:$i,B:$i]:
% 51.69/51.89     ( ( r1_xboole_0 @ A @ B ) <=>
% 51.69/51.89       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 51.69/51.89  thf('180', plain,
% 51.69/51.89      (![X0 : $i, X2 : $i]:
% 51.69/51.89         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 51.69/51.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 51.69/51.89  thf('181', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['179', '180'])).
% 51.69/51.89  thf('182', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 51.69/51.89      inference('simplify', [status(thm)], ['181'])).
% 51.69/51.89  thf('183', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 51.69/51.89          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.69/51.89          | ~ (v3_pre_topc @ X2 @ X0)
% 51.69/51.89          | ~ (r2_hidden @ X1 @ X2)
% 51.69/51.89          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 51.69/51.89      inference('demod', [status(thm)], ['174', '182'])).
% 51.69/51.89  thf('184', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0))
% 51.69/51.89          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 51.69/51.89          | ~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 51.69/51.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 51.69/51.89          | ~ (l1_pre_topc @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['171', '183'])).
% 51.69/51.89  thf('185', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 51.69/51.89          | ~ (l1_pre_topc @ sk_A)
% 51.69/51.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 51.69/51.89          | ~ (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 51.69/51.89          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['170', '184'])).
% 51.69/51.89  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('187', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 51.69/51.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 51.69/51.89          | ~ (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 51.69/51.89          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['185', '186'])).
% 51.69/51.89  thf('188', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 51.69/51.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 51.69/51.89          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 51.69/51.89      inference('simplify', [status(thm)], ['187'])).
% 51.69/51.89  thf('189', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf(t4_subset, axiom,
% 51.69/51.89    (![A:$i,B:$i,C:$i]:
% 51.69/51.89     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 51.69/51.89       ( m1_subset_1 @ A @ C ) ))).
% 51.69/51.89  thf('190', plain,
% 51.69/51.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 51.69/51.89         (~ (r2_hidden @ X24 @ X25)
% 51.69/51.89          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 51.69/51.89          | (m1_subset_1 @ X24 @ X26))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset])).
% 51.69/51.89  thf('191', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['189', '190'])).
% 51.69/51.89  thf('192', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 51.69/51.89          | ~ (v3_pre_topc @ k1_xboole_0 @ sk_A))),
% 51.69/51.89      inference('clc', [status(thm)], ['188', '191'])).
% 51.69/51.89  thf('193', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_struct_0 @ sk_A)
% 51.69/51.89          | ~ (l1_pre_topc @ sk_A)
% 51.69/51.89          | ~ (v2_pre_topc @ sk_A)
% 51.69/51.89          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['145', '192'])).
% 51.69/51.89  thf('194', plain, ((l1_struct_0 @ sk_A)),
% 51.69/51.89      inference('sup-', [status(thm)], ['71', '72'])).
% 51.69/51.89  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('197', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 51.69/51.89      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 51.69/51.89  thf('198', plain,
% 51.69/51.89      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('clc', [status(thm)], ['126', '197'])).
% 51.69/51.89  thf('199', plain,
% 51.69/51.89      (![X38 : $i]:
% 51.69/51.89         (((k2_struct_0 @ X38) = (u1_struct_0 @ X38)) | ~ (l1_struct_0 @ X38))),
% 51.69/51.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.69/51.89  thf('200', plain,
% 51.69/51.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('201', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.69/51.89        | ~ (l1_struct_0 @ sk_A))),
% 51.69/51.89      inference('sup+', [status(thm)], ['199', '200'])).
% 51.69/51.89  thf('202', plain, ((l1_struct_0 @ sk_A)),
% 51.69/51.89      inference('sup-', [status(thm)], ['71', '72'])).
% 51.69/51.89  thf('203', plain,
% 51.69/51.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.69/51.89      inference('demod', [status(thm)], ['201', '202'])).
% 51.69/51.89  thf('204', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 51.69/51.89          | ~ (l1_pre_topc @ X0))),
% 51.69/51.89      inference('clc', [status(thm)], ['46', '56'])).
% 51.69/51.89  thf('205', plain,
% 51.69/51.89      ((((v3_pre_topc @ k1_xboole_0 @ sk_A) | (v1_tops_1 @ sk_B @ sk_A)))
% 51.69/51.89         <= ((![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('simplify', [status(thm)], ['74'])).
% 51.69/51.89  thf('206', plain,
% 51.69/51.89      (((r1_xboole_0 @ sk_B @ sk_C) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('207', plain,
% 51.69/51.89      ((~ (v1_tops_1 @ sk_B @ sk_A)) <= (~ ((v1_tops_1 @ sk_B @ sk_A)))),
% 51.69/51.89      inference('split', [status(esa)], ['206'])).
% 51.69/51.89  thf('208', plain,
% 51.69/51.89      (((v3_pre_topc @ k1_xboole_0 @ sk_A))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['205', '207'])).
% 51.69/51.89  thf('209', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['86', '97', '110'])).
% 51.69/51.89  thf('210', plain,
% 51.69/51.89      ((((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['208', '209'])).
% 51.69/51.89  thf('211', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('212', plain,
% 51.69/51.89      (((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('demod', [status(thm)], ['210', '211'])).
% 51.69/51.89  thf('213', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 51.69/51.89          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['115', '116'])).
% 51.69/51.89  thf('214', plain,
% 51.69/51.89      (((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 51.69/51.89         | ~ (l1_pre_topc @ sk_A)))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['212', '213'])).
% 51.69/51.89  thf('215', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('216', plain,
% 51.69/51.89      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A)))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('demod', [status(thm)], ['214', '215'])).
% 51.69/51.89  thf('217', plain,
% 51.69/51.89      (((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A)))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup+', [status(thm)], ['204', '216'])).
% 51.69/51.89  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('219', plain,
% 51.69/51.89      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('demod', [status(thm)], ['217', '218'])).
% 51.69/51.89  thf('220', plain,
% 51.69/51.89      (![X46 : $i, X47 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 51.69/51.89          | ((k2_pre_topc @ X47 @ X46) != (k2_struct_0 @ X47))
% 51.69/51.89          | (v1_tops_1 @ X46 @ X47)
% 51.69/51.89          | ~ (l1_pre_topc @ X47))),
% 51.69/51.89      inference('cnf', [status(esa)], [d3_tops_1])).
% 51.69/51.89  thf('221', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.69/51.89           | ~ (l1_pre_topc @ sk_A)
% 51.69/51.89           | (v1_tops_1 @ X0 @ sk_A)
% 51.69/51.89           | ((k2_pre_topc @ sk_A @ X0) != (k2_struct_0 @ sk_A))))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['219', '220'])).
% 51.69/51.89  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('223', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.69/51.89           | (v1_tops_1 @ X0 @ sk_A)
% 51.69/51.89           | ((k2_pre_topc @ sk_A @ X0) != (k2_struct_0 @ sk_A))))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('demod', [status(thm)], ['221', '222'])).
% 51.69/51.89  thf('224', plain,
% 51.69/51.89      (((((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A))
% 51.69/51.89         | (v1_tops_1 @ sk_B @ sk_A)))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['203', '223'])).
% 51.69/51.89  thf('225', plain,
% 51.69/51.89      ((~ (v1_tops_1 @ sk_B @ sk_A)) <= (~ ((v1_tops_1 @ sk_B @ sk_A)))),
% 51.69/51.89      inference('split', [status(esa)], ['206'])).
% 51.69/51.89  thf('226', plain,
% 51.69/51.89      ((((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('clc', [status(thm)], ['224', '225'])).
% 51.69/51.89  thf('227', plain,
% 51.69/51.89      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 51.69/51.89         <= (~ ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             (![X52 : $i]:
% 51.69/51.89                (((X52) = (k1_xboole_0))
% 51.69/51.89                 | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89                 | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89                 | ~ (r1_xboole_0 @ sk_B @ X52))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['198', '226'])).
% 51.69/51.89  thf('228', plain,
% 51.69/51.89      (~
% 51.69/51.89       (![X52 : $i]:
% 51.69/51.89          (((X52) = (k1_xboole_0))
% 51.69/51.89           | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89           | ~ (v3_pre_topc @ X52 @ sk_A)
% 51.69/51.89           | ~ (r1_xboole_0 @ sk_B @ X52))) | 
% 51.69/51.89       ((v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('simplify', [status(thm)], ['227'])).
% 51.69/51.89  thf('229', plain,
% 51.69/51.89      (((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('split', [status(esa)], ['206'])).
% 51.69/51.89  thf('230', plain,
% 51.69/51.89      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('231', plain,
% 51.69/51.89      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('split', [status(esa)], ['230'])).
% 51.69/51.89  thf('232', plain,
% 51.69/51.89      ((((sk_C) != (k1_xboole_0)) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('233', plain,
% 51.69/51.89      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('split', [status(esa)], ['232'])).
% 51.69/51.89  thf('234', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('235', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 51.69/51.89       ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('split', [status(esa)], ['234'])).
% 51.69/51.89  thf('236', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('split', [status(esa)], ['234'])).
% 51.69/51.89  thf('237', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf('238', plain,
% 51.69/51.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.89          | (r2_hidden @ (sk_D @ X34 @ X32 @ X33) @ (u1_struct_0 @ X33))
% 51.69/51.89          | ((X34) = (k2_pre_topc @ X33 @ X32))
% 51.69/51.89          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.89          | ~ (l1_pre_topc @ X33))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 51.69/51.89  thf('239', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.69/51.89          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 51.69/51.89          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0)))),
% 51.69/51.89      inference('sup-', [status(thm)], ['237', '238'])).
% 51.69/51.89  thf('240', plain,
% 51.69/51.89      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 51.69/51.89         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 51.69/51.89         | ~ (l1_pre_topc @ sk_A)))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['236', '239'])).
% 51.69/51.89  thf('241', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['168', '169'])).
% 51.69/51.89  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('243', plain,
% 51.69/51.89      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 51.69/51.89         | ((sk_C) = (k1_xboole_0))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('demod', [status(thm)], ['240', '241', '242'])).
% 51.69/51.89  thf('244', plain,
% 51.69/51.89      (![X0 : $i]: (v4_pre_topc @ (k5_xboole_0 @ X0 @ X0) @ sk_A)),
% 51.69/51.89      inference('demod', [status(thm)], ['159', '160', '161'])).
% 51.69/51.89  thf('245', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['100', '105'])).
% 51.69/51.89  thf('246', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf('247', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 51.69/51.89      inference('sup+', [status(thm)], ['245', '246'])).
% 51.69/51.89  thf('248', plain,
% 51.69/51.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['87', '88'])).
% 51.69/51.89  thf('249', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 51.69/51.89      inference('demod', [status(thm)], ['247', '248'])).
% 51.69/51.89  thf('250', plain,
% 51.69/51.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 51.69/51.89      inference('sup+', [status(thm)], ['94', '95'])).
% 51.69/51.89  thf('251', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (m1_subset_1 @ (k5_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 51.69/51.89      inference('demod', [status(thm)], ['249', '250'])).
% 51.69/51.89  thf('252', plain,
% 51.69/51.89      (![X50 : $i, X51 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 51.69/51.89          | ~ (v4_pre_topc @ X50 @ X51)
% 51.69/51.89          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50) @ X51)
% 51.69/51.89          | ~ (l1_pre_topc @ X51))),
% 51.69/51.89      inference('cnf', [status(esa)], [t29_tops_1])).
% 51.69/51.89  thf('253', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v3_pre_topc @ 
% 51.69/51.89             (k3_subset_1 @ (u1_struct_0 @ X0) @ (k5_xboole_0 @ X1 @ X1)) @ X0)
% 51.69/51.89          | ~ (v4_pre_topc @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 51.69/51.89      inference('sup-', [status(thm)], ['251', '252'])).
% 51.69/51.89  thf('254', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['108', '109'])).
% 51.69/51.89  thf('255', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['103', '104'])).
% 51.69/51.89  thf('256', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         ((k3_subset_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 51.69/51.89      inference('sup+', [status(thm)], ['254', '255'])).
% 51.69/51.89  thf('257', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 51.69/51.89          | ~ (v4_pre_topc @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 51.69/51.89      inference('demod', [status(thm)], ['253', '256'])).
% 51.69/51.89  thf('258', plain,
% 51.69/51.89      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 51.69/51.89      inference('sup-', [status(thm)], ['244', '257'])).
% 51.69/51.89  thf('259', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('260', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 51.69/51.89      inference('demod', [status(thm)], ['258', '259'])).
% 51.69/51.89  thf('261', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 51.69/51.89      inference('simplify', [status(thm)], ['181'])).
% 51.69/51.89  thf('262', plain,
% 51.69/51.89      (![X27 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 51.69/51.89         ((zip_tseitin_0 @ X27 @ X29 @ X30 @ X31)
% 51.69/51.89          | ~ (r1_xboole_0 @ X30 @ X27)
% 51.69/51.89          | ~ (r2_hidden @ X29 @ X27)
% 51.69/51.89          | ~ (v3_pre_topc @ X27 @ X31))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 51.69/51.89  thf('263', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.89         (~ (v3_pre_topc @ X0 @ X1)
% 51.69/51.89          | ~ (r2_hidden @ X2 @ X0)
% 51.69/51.89          | (zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1))),
% 51.69/51.89      inference('sup-', [status(thm)], ['261', '262'])).
% 51.69/51.89  thf('264', plain,
% 51.69/51.89      (![X0 : $i]:
% 51.69/51.89         ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0 @ sk_A)
% 51.69/51.89          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 51.69/51.89      inference('sup-', [status(thm)], ['260', '263'])).
% 51.69/51.89  thf('265', plain,
% 51.69/51.89      (((((sk_C) = (k1_xboole_0))
% 51.69/51.89         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 51.69/51.89            (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['243', '264'])).
% 51.69/51.89  thf('266', plain,
% 51.69/51.89      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.69/51.89  thf('267', plain,
% 51.69/51.89      (![X32 : $i, X33 : $i, X34 : $i, X37 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.89          | (r2_hidden @ (sk_D @ X34 @ X32 @ X33) @ X34)
% 51.69/51.89          | ~ (zip_tseitin_0 @ X37 @ (sk_D @ X34 @ X32 @ X33) @ X32 @ X33)
% 51.69/51.89          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.89          | ((X34) = (k2_pre_topc @ X33 @ X32))
% 51.69/51.89          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.69/51.89          | ~ (l1_pre_topc @ X33))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 51.69/51.89  thf('268', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ X0)
% 51.69/51.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.69/51.89          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 51.69/51.89          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.69/51.89          | ~ (zip_tseitin_0 @ X2 @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 51.69/51.89               k1_xboole_0 @ X0)
% 51.69/51.89          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 51.69/51.89      inference('sup-', [status(thm)], ['266', '267'])).
% 51.69/51.89  thf('269', plain,
% 51.69/51.89      (((((sk_C) = (k1_xboole_0))
% 51.69/51.89         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 51.69/51.89         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.69/51.89              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 51.69/51.89         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89         | ~ (l1_pre_topc @ sk_A)))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['265', '268'])).
% 51.69/51.89  thf('270', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 51.69/51.89      inference('demod', [status(thm)], ['2', '3'])).
% 51.69/51.89  thf('271', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 51.69/51.89      inference('demod', [status(thm)], ['168', '169'])).
% 51.69/51.89  thf('272', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('split', [status(esa)], ['234'])).
% 51.69/51.89  thf('273', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('274', plain,
% 51.69/51.89      (((((sk_C) = (k1_xboole_0))
% 51.69/51.89         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 51.69/51.89         | ((sk_C) = (k1_xboole_0))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('demod', [status(thm)], ['269', '270', '271', '272', '273'])).
% 51.69/51.89  thf('275', plain,
% 51.69/51.89      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 51.69/51.89         | ((sk_C) = (k1_xboole_0))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('simplify', [status(thm)], ['274'])).
% 51.69/51.89  thf('276', plain,
% 51.69/51.89      (((v1_tops_1 @ sk_B @ sk_A)) <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 51.69/51.89      inference('split', [status(esa)], ['0'])).
% 51.69/51.89  thf('277', plain,
% 51.69/51.89      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 51.69/51.89        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 51.69/51.89      inference('demod', [status(thm)], ['78', '79'])).
% 51.69/51.89  thf('278', plain,
% 51.69/51.89      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 51.69/51.89         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 51.69/51.89      inference('sup-', [status(thm)], ['276', '277'])).
% 51.69/51.89  thf('279', plain,
% 51.69/51.89      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 51.69/51.89      inference('split', [status(esa)], ['230'])).
% 51.69/51.89  thf('280', plain,
% 51.69/51.89      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 51.69/51.89      inference('split', [status(esa)], ['206'])).
% 51.69/51.89  thf('281', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('split', [status(esa)], ['234'])).
% 51.69/51.89  thf('282', plain,
% 51.69/51.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('283', plain,
% 51.69/51.89      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 51.69/51.89          | ~ (r2_hidden @ X44 @ (k2_pre_topc @ X43 @ X42))
% 51.69/51.89          | ~ (r1_xboole_0 @ X42 @ X45)
% 51.69/51.89          | ~ (r2_hidden @ X44 @ X45)
% 51.69/51.89          | ~ (v3_pre_topc @ X45 @ X43)
% 51.69/51.89          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 51.69/51.89          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X43))
% 51.69/51.89          | ~ (l1_pre_topc @ X43))),
% 51.69/51.89      inference('cnf', [status(esa)], [t54_pre_topc])).
% 51.69/51.89  thf('284', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (~ (l1_pre_topc @ sk_A)
% 51.69/51.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 51.69/51.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89          | ~ (v3_pre_topc @ X1 @ sk_A)
% 51.69/51.89          | ~ (r2_hidden @ X0 @ X1)
% 51.69/51.89          | ~ (r1_xboole_0 @ sk_B @ X1)
% 51.69/51.89          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 51.69/51.89      inference('sup-', [status(thm)], ['282', '283'])).
% 51.69/51.89  thf('285', plain, ((l1_pre_topc @ sk_A)),
% 51.69/51.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.89  thf('286', plain,
% 51.69/51.89      (![X0 : $i, X1 : $i]:
% 51.69/51.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 51.69/51.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.69/51.89          | ~ (v3_pre_topc @ X1 @ sk_A)
% 51.69/51.89          | ~ (r2_hidden @ X0 @ X1)
% 51.69/51.89          | ~ (r1_xboole_0 @ sk_B @ X1)
% 51.69/51.89          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 51.69/51.89      inference('demod', [status(thm)], ['284', '285'])).
% 51.69/51.89  thf('287', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.89           | ~ (r1_xboole_0 @ sk_B @ sk_C)
% 51.69/51.89           | ~ (r2_hidden @ X0 @ sk_C)
% 51.69/51.89           | ~ (v3_pre_topc @ sk_C @ sk_A)
% 51.69/51.89           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['281', '286'])).
% 51.69/51.89  thf('288', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 51.69/51.89           | ~ (v3_pre_topc @ sk_C @ sk_A)
% 51.69/51.89           | ~ (r2_hidden @ X0 @ sk_C)
% 51.69/51.89           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))))
% 51.69/51.89         <= (((r1_xboole_0 @ sk_B @ sk_C)) & 
% 51.69/51.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['280', '287'])).
% 51.69/51.89  thf('289', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 51.69/51.89           | ~ (r2_hidden @ X0 @ sk_C)
% 51.69/51.89           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 51.69/51.89         <= (((r1_xboole_0 @ sk_B @ sk_C)) & 
% 51.69/51.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 51.69/51.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['279', '288'])).
% 51.69/51.89  thf('290', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('split', [status(esa)], ['234'])).
% 51.69/51.89  thf('291', plain,
% 51.69/51.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 51.69/51.89         (~ (r2_hidden @ X24 @ X25)
% 51.69/51.89          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 51.69/51.89          | (m1_subset_1 @ X24 @ X26))),
% 51.69/51.89      inference('cnf', [status(esa)], [t4_subset])).
% 51.69/51.89  thf('292', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 51.69/51.89           | ~ (r2_hidden @ X0 @ sk_C)))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['290', '291'])).
% 51.69/51.89  thf('293', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          (~ (r2_hidden @ X0 @ sk_C)
% 51.69/51.89           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))))
% 51.69/51.89         <= (((r1_xboole_0 @ sk_B @ sk_C)) & 
% 51.69/51.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 51.69/51.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('clc', [status(thm)], ['289', '292'])).
% 51.69/51.89  thf('294', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          (~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 51.69/51.89           | ~ (r2_hidden @ X0 @ sk_C)))
% 51.69/51.89         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 51.69/51.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 51.69/51.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['278', '293'])).
% 51.69/51.89  thf('295', plain,
% 51.69/51.89      (![X38 : $i]:
% 51.69/51.89         (((k2_struct_0 @ X38) = (u1_struct_0 @ X38)) | ~ (l1_struct_0 @ X38))),
% 51.69/51.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.69/51.89  thf('296', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('split', [status(esa)], ['234'])).
% 51.69/51.89  thf('297', plain,
% 51.69/51.89      ((((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.69/51.89         | ~ (l1_struct_0 @ sk_A)))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup+', [status(thm)], ['295', '296'])).
% 51.69/51.89  thf('298', plain, ((l1_struct_0 @ sk_A)),
% 51.69/51.89      inference('sup-', [status(thm)], ['71', '72'])).
% 51.69/51.89  thf('299', plain,
% 51.69/51.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('demod', [status(thm)], ['297', '298'])).
% 51.69/51.89  thf(l3_subset_1, axiom,
% 51.69/51.89    (![A:$i,B:$i]:
% 51.69/51.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.69/51.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 51.69/51.89  thf('300', plain,
% 51.69/51.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 51.69/51.89         (~ (r2_hidden @ X15 @ X16)
% 51.69/51.89          | (r2_hidden @ X15 @ X17)
% 51.69/51.89          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 51.69/51.89      inference('cnf', [status(esa)], [l3_subset_1])).
% 51.69/51.89  thf('301', plain,
% 51.69/51.89      ((![X0 : $i]:
% 51.69/51.89          ((r2_hidden @ X0 @ (k2_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C)))
% 51.69/51.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['299', '300'])).
% 51.69/51.89  thf('302', plain,
% 51.69/51.89      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C))
% 51.69/51.89         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 51.69/51.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 51.69/51.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('clc', [status(thm)], ['294', '301'])).
% 51.69/51.89  thf('303', plain,
% 51.69/51.89      ((((sk_C) = (k1_xboole_0)))
% 51.69/51.89         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 51.69/51.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 51.69/51.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['275', '302'])).
% 51.69/51.89  thf('304', plain,
% 51.69/51.89      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 51.69/51.89      inference('split', [status(esa)], ['232'])).
% 51.69/51.89  thf('305', plain,
% 51.69/51.89      ((((sk_C) != (sk_C)))
% 51.69/51.89         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 51.69/51.89             ((v1_tops_1 @ sk_B @ sk_A)) & 
% 51.69/51.89             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 51.69/51.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 51.69/51.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 51.69/51.89      inference('sup-', [status(thm)], ['303', '304'])).
% 51.69/51.89  thf('306', plain,
% 51.69/51.89      (~ ((v1_tops_1 @ sk_B @ sk_A)) | 
% 51.69/51.89       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 51.69/51.89       ~ ((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 51.69/51.89       (((sk_C) = (k1_xboole_0)))),
% 51.69/51.89      inference('simplify', [status(thm)], ['305'])).
% 51.69/51.89  thf('307', plain, ($false),
% 51.69/51.89      inference('sat_resolution*', [status(thm)],
% 51.69/51.89                ['1', '228', '229', '231', '233', '235', '306'])).
% 51.69/51.89  
% 51.69/51.89  % SZS output end Refutation
% 51.69/51.89  
% 51.69/51.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
