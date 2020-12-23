%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I37OL1mgqa

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:05 EST 2020

% Result     : Theorem 12.52s
% Output     : Refutation 12.52s
% Verified   : 
% Statistics : Number of formulae       :  311 (2498 expanded)
%              Number of leaves         :   48 ( 754 expanded)
%              Depth                    :   36
%              Number of atoms          : 3691 (36423 expanded)
%              Number of equality atoms :  212 (1860 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X46: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X46 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X46 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_B @ X46 )
      | ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) )
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ X29 )
      | ( zip_tseitin_0 @ ( sk_E @ X29 @ X27 @ X28 ) @ ( sk_D @ X29 @ X27 @ X28 ) @ X27 @ X28 )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X25 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ X29 )
      | ( m1_subset_1 @ ( sk_E @ X29 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ( ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,
    ( ( ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','17'])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v3_pre_topc @ X22 @ X23 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
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
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
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
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
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
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_pre_topc @ X42 @ X41 )
       != ( k2_struct_0 @ X42 ) )
      | ( v1_tops_1 @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
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
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('56',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v1_tops_1 @ X41 @ X42 )
      | ( ( k2_pre_topc @ X42 @ X41 )
        = ( k2_struct_0 @ X42 ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
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
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup+',[status(thm)],['45','65'])).

thf('67',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('70',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('71',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
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

thf('75',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('78',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('81',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['67','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('90',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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

thf('91',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,
    ( ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('100',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('101',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('110',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup+',[status(thm)],['98','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('117',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup+',[status(thm)],['97','117'])).

thf('119',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('121',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ k1_xboole_0 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(demod,[status(thm)],['41','119','120'])).

thf('122',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('123',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('126',plain,(
    ! [X43: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('127',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('128',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('129',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('132',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['125','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('146',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('147',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( ( k2_pre_topc @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('154',plain,(
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

thf('155',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( r2_hidden @ X39 @ ( k2_pre_topc @ X38 @ X37 ) )
      | ~ ( r1_xboole_0 @ X37 @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( v3_pre_topc @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('158',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('160',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['156','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['152','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('169',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v4_pre_topc @ X44 @ X45 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['172','175'])).

thf('177',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['167','176'])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['165','166','179'])).

thf('181',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('182',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['180','183'])).

thf('185',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('186',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['184','187'])).

thf('189',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(clc,[status(thm)],['123','188'])).

thf('190',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('191',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['193'])).

thf('195',plain,
    ( ~ ! [X46: $i] :
          ( ( X46 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X46 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X46 ) )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['192','194'])).

thf('196',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['193'])).

thf('197',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['197'])).

thf('199',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['199'])).

thf('201',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['201'])).

thf('203',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['201'])).

thf('204',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('205',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['203','206'])).

thf('208',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['150','151'])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['177','178'])).

thf('212',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('213',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X25 @ X22 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( v3_pre_topc @ X22 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('214',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['211','214'])).

thf('216',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['210','215'])).

thf('217',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('218',plain,(
    ! [X27: $i,X28: $i,X29: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ X29 )
      | ~ ( zip_tseitin_0 @ X32 @ ( sk_D @ X29 @ X27 @ X28 ) @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('219',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('222',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['150','151'])).

thf('223',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['201'])).

thf('224',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['220','221','222','223','224'])).

thf('226',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['197'])).

thf('228',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['193'])).

thf('229',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X25 @ X22 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( v3_pre_topc @ X22 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('230',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v3_pre_topc @ sk_C @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_C )
        | ( zip_tseitin_0 @ sk_C @ X1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['227','230'])).

thf('232',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_B @ sk_A ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['226','231'])).

thf('233',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['201'])).

thf('234',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('235',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('236',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('238',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X29
       != ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X27 @ X28 )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('239',plain,(
    ! [X27: $i,X28: $i,X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X28 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ X31 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_hidden @ X31 @ ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_pre_topc @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['237','239'])).

thf('241',plain,
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
    inference('sup-',[status(thm)],['236','240'])).

thf('242',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('243',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('245',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('247',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['241','242','243','244','245','246'])).

thf('248',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['233','247'])).

thf('249',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['232','248'])).

thf('250',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('251',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('253',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('254',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['252','253'])).

thf('255',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('256',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['251','256'])).

thf('258',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['199'])).

thf('259',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','195','196','198','200','202','260'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I37OL1mgqa
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:31:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 12.52/12.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.52/12.70  % Solved by: fo/fo7.sh
% 12.52/12.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.52/12.70  % done 16098 iterations in 12.238s
% 12.52/12.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.52/12.70  % SZS output start Refutation
% 12.52/12.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 12.52/12.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.52/12.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 12.52/12.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 12.52/12.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.52/12.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 12.52/12.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 12.52/12.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.52/12.70  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 12.52/12.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 12.52/12.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 12.52/12.70  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 12.52/12.70  thf(sk_A_type, type, sk_A: $i).
% 12.52/12.70  thf(sk_C_type, type, sk_C: $i).
% 12.52/12.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 12.52/12.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.52/12.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.52/12.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.52/12.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.52/12.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.52/12.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 12.52/12.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 12.52/12.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 12.52/12.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 12.52/12.70  thf(sk_B_type, type, sk_B: $i).
% 12.52/12.70  thf(t80_tops_1, conjecture,
% 12.52/12.70    (![A:$i]:
% 12.52/12.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.52/12.70       ( ![B:$i]:
% 12.52/12.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.70           ( ( v1_tops_1 @ B @ A ) <=>
% 12.52/12.70             ( ![C:$i]:
% 12.52/12.70               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.70                 ( ~( ( ( C ) != ( k1_xboole_0 ) ) & ( v3_pre_topc @ C @ A ) & 
% 12.52/12.70                      ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ))).
% 12.52/12.70  thf(zf_stmt_0, negated_conjecture,
% 12.52/12.70    (~( ![A:$i]:
% 12.52/12.70        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.52/12.70          ( ![B:$i]:
% 12.52/12.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.70              ( ( v1_tops_1 @ B @ A ) <=>
% 12.52/12.70                ( ![C:$i]:
% 12.52/12.70                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.70                    ( ~( ( ( C ) != ( k1_xboole_0 ) ) & 
% 12.52/12.70                         ( v3_pre_topc @ C @ A ) & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ) )),
% 12.52/12.70    inference('cnf.neg', [status(esa)], [t80_tops_1])).
% 12.52/12.70  thf('0', plain,
% 12.52/12.70      (![X46 : $i]:
% 12.52/12.70         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.70          | ((X46) = (k1_xboole_0))
% 12.52/12.70          | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.70          | ~ (r1_xboole_0 @ sk_B @ X46)
% 12.52/12.70          | (v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.70  thf('1', plain,
% 12.52/12.70      ((![X46 : $i]:
% 12.52/12.70          (((X46) = (k1_xboole_0))
% 12.52/12.70           | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.70           | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71           | ~ (r1_xboole_0 @ sk_B @ X46))) | 
% 12.52/12.71       ((v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('split', [status(esa)], ['0'])).
% 12.52/12.71  thf(dt_k2_subset_1, axiom,
% 12.52/12.71    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 12.52/12.71  thf('2', plain,
% 12.52/12.71      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 12.52/12.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 12.52/12.71  thf('3', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 12.52/12.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 12.52/12.71  thf('4', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('5', plain,
% 12.52/12.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf(d13_pre_topc, axiom,
% 12.52/12.71    (![A:$i]:
% 12.52/12.71     ( ( l1_pre_topc @ A ) =>
% 12.52/12.71       ( ![B:$i]:
% 12.52/12.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71           ( ![C:$i]:
% 12.52/12.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 12.52/12.71                 ( ![D:$i]:
% 12.52/12.71                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 12.52/12.71                     ( ( r2_hidden @ D @ C ) <=>
% 12.52/12.71                       ( ![E:$i]:
% 12.52/12.71                         ( ( m1_subset_1 @
% 12.52/12.71                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71                           ( ~( ( r1_xboole_0 @ B @ E ) & 
% 12.52/12.71                                ( r2_hidden @ D @ E ) & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.52/12.71  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 12.52/12.71  thf(zf_stmt_2, axiom,
% 12.52/12.71    (![E:$i,D:$i,B:$i,A:$i]:
% 12.52/12.71     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 12.52/12.71       ( ( v3_pre_topc @ E @ A ) & ( r2_hidden @ D @ E ) & 
% 12.52/12.71         ( r1_xboole_0 @ B @ E ) ) ))).
% 12.52/12.71  thf(zf_stmt_3, axiom,
% 12.52/12.71    (![A:$i]:
% 12.52/12.71     ( ( l1_pre_topc @ A ) =>
% 12.52/12.71       ( ![B:$i]:
% 12.52/12.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71           ( ![C:$i]:
% 12.52/12.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 12.52/12.71                 ( ![D:$i]:
% 12.52/12.71                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 12.52/12.71                     ( ( r2_hidden @ D @ C ) <=>
% 12.52/12.71                       ( ![E:$i]:
% 12.52/12.71                         ( ( m1_subset_1 @
% 12.52/12.71                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71                           ( ~( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.52/12.71  thf('6', plain,
% 12.52/12.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ X29)
% 12.52/12.71          | (zip_tseitin_0 @ (sk_E @ X29 @ X27 @ X28) @ 
% 12.52/12.71             (sk_D @ X29 @ X27 @ X28) @ X27 @ X28)
% 12.52/12.71          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 12.52/12.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (l1_pre_topc @ X28))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.52/12.71  thf('7', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ sk_A)
% 12.52/12.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 12.52/12.71             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 12.52/12.71          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['5', '6'])).
% 12.52/12.71  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('9', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 12.52/12.71             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 12.52/12.71          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 12.52/12.71      inference('demod', [status(thm)], ['7', '8'])).
% 12.52/12.71  thf('10', plain,
% 12.52/12.71      ((~ (r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71           (u1_struct_0 @ sk_A))
% 12.52/12.71        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 12.52/12.71        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['4', '9'])).
% 12.52/12.71  thf('11', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('12', plain,
% 12.52/12.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('13', plain,
% 12.52/12.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ (u1_struct_0 @ X28))
% 12.52/12.71          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 12.52/12.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (l1_pre_topc @ X28))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.52/12.71  thf('14', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ sk_A)
% 12.52/12.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['12', '13'])).
% 12.52/12.71  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('16', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('demod', [status(thm)], ['14', '15'])).
% 12.52/12.71  thf('17', plain,
% 12.52/12.71      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71         (u1_struct_0 @ sk_A))
% 12.52/12.71        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['11', '16'])).
% 12.52/12.71  thf('18', plain,
% 12.52/12.71      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 12.52/12.71      inference('clc', [status(thm)], ['10', '17'])).
% 12.52/12.71  thf('19', plain,
% 12.52/12.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 12.52/12.71         ((r1_xboole_0 @ X25 @ X22) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.52/12.71  thf('20', plain,
% 12.52/12.71      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['18', '19'])).
% 12.52/12.71  thf('21', plain,
% 12.52/12.71      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71         (u1_struct_0 @ sk_A))
% 12.52/12.71        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['11', '16'])).
% 12.52/12.71  thf('22', plain,
% 12.52/12.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('23', plain,
% 12.52/12.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ X29)
% 12.52/12.71          | (m1_subset_1 @ (sk_E @ X29 @ X27 @ X28) @ 
% 12.52/12.71             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 12.52/12.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (l1_pre_topc @ X28))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.52/12.71  thf('24', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ sk_A)
% 12.52/12.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 12.52/12.71             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['22', '23'])).
% 12.52/12.71  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('26', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 12.52/12.71             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 12.52/12.71      inference('demod', [status(thm)], ['24', '25'])).
% 12.52/12.71  thf('27', plain,
% 12.52/12.71      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.52/12.71             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['21', '26'])).
% 12.52/12.71  thf('28', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('29', plain,
% 12.52/12.71      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 12.52/12.71      inference('demod', [status(thm)], ['27', '28'])).
% 12.52/12.71  thf('30', plain,
% 12.52/12.71      (((m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 12.52/12.71      inference('simplify', [status(thm)], ['29'])).
% 12.52/12.71  thf('31', plain,
% 12.52/12.71      ((![X46 : $i]:
% 12.52/12.71          (((X46) = (k1_xboole_0))
% 12.52/12.71           | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71           | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71           | ~ (r1_xboole_0 @ sk_B @ X46)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('split', [status(esa)], ['0'])).
% 12.52/12.71  thf('32', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | ~ (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A))
% 12.52/12.71         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 12.52/12.71         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['30', '31'])).
% 12.52/12.71  thf('33', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 12.52/12.71         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['20', '32'])).
% 12.52/12.71  thf('34', plain,
% 12.52/12.71      (((~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 12.52/12.71         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['33'])).
% 12.52/12.71  thf('35', plain,
% 12.52/12.71      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 12.52/12.71      inference('clc', [status(thm)], ['10', '17'])).
% 12.52/12.71  thf('36', plain,
% 12.52/12.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 12.52/12.71         ((v3_pre_topc @ X22 @ X23) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.52/12.71  thf('37', plain,
% 12.52/12.71      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 12.52/12.71      inference('sup-', [status(thm)], ['35', '36'])).
% 12.52/12.71  thf('38', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('clc', [status(thm)], ['34', '37'])).
% 12.52/12.71  thf('39', plain,
% 12.52/12.71      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | (zip_tseitin_0 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 12.52/12.71      inference('clc', [status(thm)], ['10', '17'])).
% 12.52/12.71  thf('40', plain,
% 12.52/12.71      ((((zip_tseitin_0 @ k1_xboole_0 @ 
% 12.52/12.71          (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup+', [status(thm)], ['38', '39'])).
% 12.52/12.71  thf('41', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | (zip_tseitin_0 @ k1_xboole_0 @ 
% 12.52/12.71            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['40'])).
% 12.52/12.71  thf('42', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('clc', [status(thm)], ['34', '37'])).
% 12.52/12.71  thf('43', plain,
% 12.52/12.71      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71        | (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 12.52/12.71      inference('sup-', [status(thm)], ['35', '36'])).
% 12.52/12.71  thf('44', plain,
% 12.52/12.71      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup+', [status(thm)], ['42', '43'])).
% 12.52/12.71  thf('45', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['44'])).
% 12.52/12.71  thf(d3_struct_0, axiom,
% 12.52/12.71    (![A:$i]:
% 12.52/12.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 12.52/12.71  thf('46', plain,
% 12.52/12.71      (![X33 : $i]:
% 12.52/12.71         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.52/12.71  thf('47', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['44'])).
% 12.52/12.71  thf('48', plain,
% 12.52/12.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf(d3_tops_1, axiom,
% 12.52/12.71    (![A:$i]:
% 12.52/12.71     ( ( l1_pre_topc @ A ) =>
% 12.52/12.71       ( ![B:$i]:
% 12.52/12.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71           ( ( v1_tops_1 @ B @ A ) <=>
% 12.52/12.71             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 12.52/12.71  thf('49', plain,
% 12.52/12.71      (![X41 : $i, X42 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 12.52/12.71          | ((k2_pre_topc @ X42 @ X41) != (k2_struct_0 @ X42))
% 12.52/12.71          | (v1_tops_1 @ X41 @ X42)
% 12.52/12.71          | ~ (l1_pre_topc @ X42))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_tops_1])).
% 12.52/12.71  thf('50', plain,
% 12.52/12.71      ((~ (l1_pre_topc @ sk_A)
% 12.52/12.71        | (v1_tops_1 @ sk_B @ sk_A)
% 12.52/12.71        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['48', '49'])).
% 12.52/12.71  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('52', plain,
% 12.52/12.71      (((v1_tops_1 @ sk_B @ sk_A)
% 12.52/12.71        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 12.52/12.71      inference('demod', [status(thm)], ['50', '51'])).
% 12.52/12.71  thf('53', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 12.52/12.71         | (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 12.52/12.71         | (v1_tops_1 @ sk_B @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['47', '52'])).
% 12.52/12.71  thf('54', plain,
% 12.52/12.71      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 12.52/12.71         | ~ (l1_struct_0 @ sk_A)
% 12.52/12.71         | (v1_tops_1 @ sk_B @ sk_A)
% 12.52/12.71         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['46', '53'])).
% 12.52/12.71  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf(dt_l1_pre_topc, axiom,
% 12.52/12.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 12.52/12.71  thf('56', plain,
% 12.52/12.71      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 12.52/12.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 12.52/12.71  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 12.52/12.71      inference('sup-', [status(thm)], ['55', '56'])).
% 12.52/12.71  thf('58', plain,
% 12.52/12.71      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 12.52/12.71         | (v1_tops_1 @ sk_B @ sk_A)
% 12.52/12.71         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('demod', [status(thm)], ['54', '57'])).
% 12.52/12.71  thf('59', plain,
% 12.52/12.71      ((((v3_pre_topc @ k1_xboole_0 @ sk_A) | (v1_tops_1 @ sk_B @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['58'])).
% 12.52/12.71  thf('60', plain,
% 12.52/12.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('61', plain,
% 12.52/12.71      (![X41 : $i, X42 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 12.52/12.71          | ~ (v1_tops_1 @ X41 @ X42)
% 12.52/12.71          | ((k2_pre_topc @ X42 @ X41) = (k2_struct_0 @ X42))
% 12.52/12.71          | ~ (l1_pre_topc @ X42))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_tops_1])).
% 12.52/12.71  thf('62', plain,
% 12.52/12.71      ((~ (l1_pre_topc @ sk_A)
% 12.52/12.71        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 12.52/12.71        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('sup-', [status(thm)], ['60', '61'])).
% 12.52/12.71  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('64', plain,
% 12.52/12.71      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 12.52/12.71        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('demod', [status(thm)], ['62', '63'])).
% 12.52/12.71  thf('65', plain,
% 12.52/12.71      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 12.52/12.71         | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['59', '64'])).
% 12.52/12.71  thf('66', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 12.52/12.71         | (v3_pre_topc @ k1_xboole_0 @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup+', [status(thm)], ['45', '65'])).
% 12.52/12.71  thf('67', plain,
% 12.52/12.71      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['66'])).
% 12.52/12.71  thf('68', plain,
% 12.52/12.71      (![X33 : $i]:
% 12.52/12.71         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.52/12.71  thf('69', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('70', plain,
% 12.52/12.71      (![X33 : $i]:
% 12.52/12.71         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.52/12.71  thf(t29_tops_1, axiom,
% 12.52/12.71    (![A:$i]:
% 12.52/12.71     ( ( l1_pre_topc @ A ) =>
% 12.52/12.71       ( ![B:$i]:
% 12.52/12.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71           ( ( v4_pre_topc @ B @ A ) <=>
% 12.52/12.71             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 12.52/12.71  thf('71', plain,
% 12.52/12.71      (![X44 : $i, X45 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 12.52/12.71          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 12.52/12.71          | (v4_pre_topc @ X44 @ X45)
% 12.52/12.71          | ~ (l1_pre_topc @ X45))),
% 12.52/12.71      inference('cnf', [status(esa)], [t29_tops_1])).
% 12.52/12.71  thf('72', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v4_pre_topc @ X1 @ X0)
% 12.52/12.71          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['70', '71'])).
% 12.52/12.71  thf('73', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (v3_pre_topc @ 
% 12.52/12.71             (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ X0)
% 12.52/12.71          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['69', '72'])).
% 12.52/12.71  thf('74', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (v3_pre_topc @ 
% 12.52/12.71             (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['68', '73'])).
% 12.52/12.71  thf('75', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf(d5_subset_1, axiom,
% 12.52/12.71    (![A:$i,B:$i]:
% 12.52/12.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 12.52/12.71       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 12.52/12.71  thf('76', plain,
% 12.52/12.71      (![X10 : $i, X11 : $i]:
% 12.52/12.71         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 12.52/12.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 12.52/12.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 12.52/12.71  thf('77', plain,
% 12.52/12.71      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['75', '76'])).
% 12.52/12.71  thf(t3_boole, axiom,
% 12.52/12.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 12.52/12.71  thf('78', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 12.52/12.71      inference('cnf', [status(esa)], [t3_boole])).
% 12.52/12.71  thf(t48_xboole_1, axiom,
% 12.52/12.71    (![A:$i,B:$i]:
% 12.52/12.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 12.52/12.71  thf('79', plain,
% 12.52/12.71      (![X7 : $i, X8 : $i]:
% 12.52/12.71         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 12.52/12.71           = (k3_xboole_0 @ X7 @ X8))),
% 12.52/12.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.52/12.71  thf('80', plain,
% 12.52/12.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 12.52/12.71      inference('sup+', [status(thm)], ['78', '79'])).
% 12.52/12.71  thf(t2_boole, axiom,
% 12.52/12.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 12.52/12.71  thf('81', plain,
% 12.52/12.71      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 12.52/12.71      inference('cnf', [status(esa)], [t2_boole])).
% 12.52/12.71  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['80', '81'])).
% 12.52/12.71  thf('83', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v4_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 12.52/12.71      inference('demod', [status(thm)], ['74', '77', '82'])).
% 12.52/12.71  thf('84', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         ((v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 12.52/12.71      inference('simplify', [status(thm)], ['83'])).
% 12.52/12.71  thf('85', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | ~ (l1_struct_0 @ sk_A)
% 12.52/12.71         | ~ (l1_pre_topc @ sk_A)
% 12.52/12.71         | (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['67', '84'])).
% 12.52/12.71  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 12.52/12.71      inference('sup-', [status(thm)], ['55', '56'])).
% 12.52/12.71  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('88', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('demod', [status(thm)], ['85', '86', '87'])).
% 12.52/12.71  thf('89', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('90', plain,
% 12.52/12.71      (![X33 : $i]:
% 12.52/12.71         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.52/12.71  thf(t52_pre_topc, axiom,
% 12.52/12.71    (![A:$i]:
% 12.52/12.71     ( ( l1_pre_topc @ A ) =>
% 12.52/12.71       ( ![B:$i]:
% 12.52/12.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 12.52/12.71             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 12.52/12.71               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 12.52/12.71  thf('91', plain,
% 12.52/12.71      (![X35 : $i, X36 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 12.52/12.71          | ~ (v4_pre_topc @ X35 @ X36)
% 12.52/12.71          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 12.52/12.71          | ~ (l1_pre_topc @ X36))),
% 12.52/12.71      inference('cnf', [status(esa)], [t52_pre_topc])).
% 12.52/12.71  thf('92', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 12.52/12.71          | ~ (v4_pre_topc @ X1 @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['90', '91'])).
% 12.52/12.71  thf('93', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 12.52/12.71          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['89', '92'])).
% 12.52/12.71  thf('94', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | ~ (l1_struct_0 @ sk_A)
% 12.52/12.71         | ~ (l1_pre_topc @ sk_A)
% 12.52/12.71         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['88', '93'])).
% 12.52/12.71  thf('95', plain, ((l1_struct_0 @ sk_A)),
% 12.52/12.71      inference('sup-', [status(thm)], ['55', '56'])).
% 12.52/12.71  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('97', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('demod', [status(thm)], ['94', '95', '96'])).
% 12.52/12.71  thf('98', plain,
% 12.52/12.71      (![X33 : $i]:
% 12.52/12.71         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.52/12.71  thf('99', plain,
% 12.52/12.71      ((((v3_pre_topc @ k1_xboole_0 @ sk_A)
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['66'])).
% 12.52/12.71  thf('100', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('101', plain,
% 12.52/12.71      (![X44 : $i, X45 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 12.52/12.71          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 12.52/12.71          | (v4_pre_topc @ X44 @ X45)
% 12.52/12.71          | ~ (l1_pre_topc @ X45))),
% 12.52/12.71      inference('cnf', [status(esa)], [t29_tops_1])).
% 12.52/12.71  thf('102', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.52/12.71          | ~ (v3_pre_topc @ 
% 12.52/12.71               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['100', '101'])).
% 12.52/12.71  thf('103', plain,
% 12.52/12.71      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['75', '76'])).
% 12.52/12.71  thf('104', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['80', '81'])).
% 12.52/12.71  thf('105', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.52/12.71          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 12.52/12.71      inference('demod', [status(thm)], ['102', '103', '104'])).
% 12.52/12.71  thf('106', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 12.52/12.71         | ~ (l1_pre_topc @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['99', '105'])).
% 12.52/12.71  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('108', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('demod', [status(thm)], ['106', '107'])).
% 12.52/12.71  thf('109', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('110', plain,
% 12.52/12.71      (![X35 : $i, X36 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 12.52/12.71          | ~ (v4_pre_topc @ X35 @ X36)
% 12.52/12.71          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 12.52/12.71          | ~ (l1_pre_topc @ X36))),
% 12.52/12.71      inference('cnf', [status(esa)], [t52_pre_topc])).
% 12.52/12.71  thf('111', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 12.52/12.71          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['109', '110'])).
% 12.52/12.71  thf('112', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 12.52/12.71         | ~ (l1_pre_topc @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['108', '111'])).
% 12.52/12.71  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('114', plain,
% 12.52/12.71      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('demod', [status(thm)], ['112', '113'])).
% 12.52/12.71  thf('115', plain,
% 12.52/12.71      (((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 12.52/12.71         | ~ (l1_struct_0 @ sk_A)
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup+', [status(thm)], ['98', '114'])).
% 12.52/12.71  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 12.52/12.71      inference('sup-', [status(thm)], ['55', '56'])).
% 12.52/12.71  thf('117', plain,
% 12.52/12.71      (((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('demod', [status(thm)], ['115', '116'])).
% 12.52/12.71  thf('118', plain,
% 12.52/12.71      (((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 12.52/12.71         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup+', [status(thm)], ['97', '117'])).
% 12.52/12.71  thf('119', plain,
% 12.52/12.71      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['118'])).
% 12.52/12.71  thf('120', plain,
% 12.52/12.71      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['118'])).
% 12.52/12.71  thf('121', plain,
% 12.52/12.71      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | (zip_tseitin_0 @ k1_xboole_0 @ 
% 12.52/12.71            (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('demod', [status(thm)], ['41', '119', '120'])).
% 12.52/12.71  thf('122', plain,
% 12.52/12.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 12.52/12.71         ((r2_hidden @ X24 @ X22) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.52/12.71  thf('123', plain,
% 12.52/12.71      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71         | (r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 12.52/12.71            k1_xboole_0)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['121', '122'])).
% 12.52/12.71  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('125', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['80', '81'])).
% 12.52/12.71  thf(fc10_tops_1, axiom,
% 12.52/12.71    (![A:$i]:
% 12.52/12.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.52/12.71       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 12.52/12.71  thf('126', plain,
% 12.52/12.71      (![X43 : $i]:
% 12.52/12.71         ((v3_pre_topc @ (k2_struct_0 @ X43) @ X43)
% 12.52/12.71          | ~ (l1_pre_topc @ X43)
% 12.52/12.71          | ~ (v2_pre_topc @ X43))),
% 12.52/12.71      inference('cnf', [status(esa)], [fc10_tops_1])).
% 12.52/12.71  thf('127', plain,
% 12.52/12.71      (![X33 : $i]:
% 12.52/12.71         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.52/12.71  thf(t4_subset_1, axiom,
% 12.52/12.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 12.52/12.71  thf('128', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf('129', plain,
% 12.52/12.71      (![X44 : $i, X45 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 12.52/12.71          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 12.52/12.71          | (v4_pre_topc @ X44 @ X45)
% 12.52/12.71          | ~ (l1_pre_topc @ X45))),
% 12.52/12.71      inference('cnf', [status(esa)], [t29_tops_1])).
% 12.52/12.71  thf('130', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 12.52/12.71          | ~ (v3_pre_topc @ 
% 12.52/12.71               (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['128', '129'])).
% 12.52/12.71  thf('131', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf('132', plain,
% 12.52/12.71      (![X10 : $i, X11 : $i]:
% 12.52/12.71         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 12.52/12.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 12.52/12.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 12.52/12.71  thf('133', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['131', '132'])).
% 12.52/12.71  thf('134', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 12.52/12.71      inference('cnf', [status(esa)], [t3_boole])).
% 12.52/12.71  thf('135', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 12.52/12.71      inference('demod', [status(thm)], ['133', '134'])).
% 12.52/12.71  thf('136', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 12.52/12.71          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 12.52/12.71      inference('demod', [status(thm)], ['130', '135'])).
% 12.52/12.71  thf('137', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['127', '136'])).
% 12.52/12.71  thf('138', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (v2_pre_topc @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 12.52/12.71          | ~ (l1_struct_0 @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['126', '137'])).
% 12.52/12.71  thf('139', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_struct_0 @ X0)
% 12.52/12.71          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 12.52/12.71          | ~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (v2_pre_topc @ X0))),
% 12.52/12.71      inference('simplify', [status(thm)], ['138'])).
% 12.52/12.71  thf('140', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         ((v4_pre_topc @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 12.52/12.71          | ~ (v2_pre_topc @ X1)
% 12.52/12.71          | ~ (l1_pre_topc @ X1)
% 12.52/12.71          | ~ (l1_struct_0 @ X1))),
% 12.52/12.71      inference('sup+', [status(thm)], ['125', '139'])).
% 12.52/12.71  thf('141', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_struct_0 @ sk_A)
% 12.52/12.71          | ~ (v2_pre_topc @ sk_A)
% 12.52/12.71          | (v4_pre_topc @ (k4_xboole_0 @ X0 @ X0) @ sk_A))),
% 12.52/12.71      inference('sup-', [status(thm)], ['124', '140'])).
% 12.52/12.71  thf('142', plain, ((l1_struct_0 @ sk_A)),
% 12.52/12.71      inference('sup-', [status(thm)], ['55', '56'])).
% 12.52/12.71  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('144', plain,
% 12.52/12.71      (![X0 : $i]: (v4_pre_topc @ (k4_xboole_0 @ X0 @ X0) @ sk_A)),
% 12.52/12.71      inference('demod', [status(thm)], ['141', '142', '143'])).
% 12.52/12.71  thf('145', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['80', '81'])).
% 12.52/12.71  thf('146', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf('147', plain,
% 12.52/12.71      (![X35 : $i, X36 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 12.52/12.71          | ~ (v4_pre_topc @ X35 @ X36)
% 12.52/12.71          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 12.52/12.71          | ~ (l1_pre_topc @ X36))),
% 12.52/12.71      inference('cnf', [status(esa)], [t52_pre_topc])).
% 12.52/12.71  thf('148', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 12.52/12.71          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['146', '147'])).
% 12.52/12.71  thf('149', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         (~ (v4_pre_topc @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 12.52/12.71          | ((k2_pre_topc @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 12.52/12.71          | ~ (l1_pre_topc @ X1))),
% 12.52/12.71      inference('sup-', [status(thm)], ['145', '148'])).
% 12.52/12.71  thf('150', plain,
% 12.52/12.71      ((~ (l1_pre_topc @ sk_A)
% 12.52/12.71        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['144', '149'])).
% 12.52/12.71  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('152', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['150', '151'])).
% 12.52/12.71  thf('153', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('154', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf(t54_pre_topc, axiom,
% 12.52/12.71    (![A:$i]:
% 12.52/12.71     ( ( l1_pre_topc @ A ) =>
% 12.52/12.71       ( ![B:$i]:
% 12.52/12.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71           ( ![C:$i]:
% 12.52/12.71             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.52/12.71               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 12.52/12.71                 ( ( ~( v2_struct_0 @ A ) ) & 
% 12.52/12.71                   ( ![D:$i]:
% 12.52/12.71                     ( ( m1_subset_1 @
% 12.52/12.71                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.52/12.71                       ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 12.52/12.71                            ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.52/12.71  thf('155', plain,
% 12.52/12.71      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 12.52/12.71          | ~ (r2_hidden @ X39 @ (k2_pre_topc @ X38 @ X37))
% 12.52/12.71          | ~ (r1_xboole_0 @ X37 @ X40)
% 12.52/12.71          | ~ (r2_hidden @ X39 @ X40)
% 12.52/12.71          | ~ (v3_pre_topc @ X40 @ X38)
% 12.52/12.71          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 12.52/12.71          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 12.52/12.71          | ~ (l1_pre_topc @ X38))),
% 12.52/12.71      inference('cnf', [status(esa)], [t54_pre_topc])).
% 12.52/12.71  thf('156', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.52/12.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.52/12.71          | ~ (v3_pre_topc @ X2 @ X0)
% 12.52/12.71          | ~ (r2_hidden @ X1 @ X2)
% 12.52/12.71          | ~ (r1_xboole_0 @ k1_xboole_0 @ X2)
% 12.52/12.71          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['154', '155'])).
% 12.52/12.71  thf(commutativity_k3_xboole_0, axiom,
% 12.52/12.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 12.52/12.71  thf('157', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.52/12.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.52/12.71  thf('158', plain,
% 12.52/12.71      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 12.52/12.71      inference('cnf', [status(esa)], [t2_boole])).
% 12.52/12.71  thf('159', plain,
% 12.52/12.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 12.52/12.71      inference('sup+', [status(thm)], ['157', '158'])).
% 12.52/12.71  thf(d7_xboole_0, axiom,
% 12.52/12.71    (![A:$i,B:$i]:
% 12.52/12.71     ( ( r1_xboole_0 @ A @ B ) <=>
% 12.52/12.71       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 12.52/12.71  thf('160', plain,
% 12.52/12.71      (![X2 : $i, X4 : $i]:
% 12.52/12.71         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 12.52/12.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.52/12.71  thf('161', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['159', '160'])).
% 12.52/12.71  thf('162', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 12.52/12.71      inference('simplify', [status(thm)], ['161'])).
% 12.52/12.71  thf('163', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.52/12.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.52/12.71          | ~ (v3_pre_topc @ X2 @ X0)
% 12.52/12.71          | ~ (r2_hidden @ X1 @ X2)
% 12.52/12.71          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 12.52/12.71      inference('demod', [status(thm)], ['156', '162'])).
% 12.52/12.71  thf('164', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         (~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0))
% 12.52/12.71          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 12.52/12.71          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.52/12.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.52/12.71          | ~ (l1_pre_topc @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['153', '163'])).
% 12.52/12.71  thf('165', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 12.52/12.71          | ~ (l1_pre_topc @ sk_A)
% 12.52/12.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.52/12.71          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 12.52/12.71          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['152', '164'])).
% 12.52/12.71  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('167', plain,
% 12.52/12.71      (![X0 : $i]: (v4_pre_topc @ (k4_xboole_0 @ X0 @ X0) @ sk_A)),
% 12.52/12.71      inference('demod', [status(thm)], ['141', '142', '143'])).
% 12.52/12.71  thf('168', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['80', '81'])).
% 12.52/12.71  thf('169', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf('170', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 12.52/12.71      inference('sup+', [status(thm)], ['168', '169'])).
% 12.52/12.71  thf('171', plain,
% 12.52/12.71      (![X44 : $i, X45 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 12.52/12.71          | ~ (v4_pre_topc @ X44 @ X45)
% 12.52/12.71          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 12.52/12.71          | ~ (l1_pre_topc @ X45))),
% 12.52/12.71      inference('cnf', [status(esa)], [t29_tops_1])).
% 12.52/12.71  thf('172', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v3_pre_topc @ 
% 12.52/12.71             (k3_subset_1 @ (u1_struct_0 @ X0) @ (k4_xboole_0 @ X1 @ X1)) @ X0)
% 12.52/12.71          | ~ (v4_pre_topc @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['170', '171'])).
% 12.52/12.71  thf('173', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['80', '81'])).
% 12.52/12.71  thf('174', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 12.52/12.71      inference('demod', [status(thm)], ['133', '134'])).
% 12.52/12.71  thf('175', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 12.52/12.71      inference('sup+', [status(thm)], ['173', '174'])).
% 12.52/12.71  thf('176', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.52/12.71          | ~ (v4_pre_topc @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 12.52/12.71      inference('demod', [status(thm)], ['172', '175'])).
% 12.52/12.71  thf('177', plain,
% 12.52/12.71      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 12.52/12.71      inference('sup-', [status(thm)], ['167', '176'])).
% 12.52/12.71  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('179', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 12.52/12.71      inference('demod', [status(thm)], ['177', '178'])).
% 12.52/12.71  thf('180', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 12.52/12.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.52/12.71          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('demod', [status(thm)], ['165', '166', '179'])).
% 12.52/12.71  thf('181', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf(t4_subset, axiom,
% 12.52/12.71    (![A:$i,B:$i,C:$i]:
% 12.52/12.71     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 12.52/12.71       ( m1_subset_1 @ A @ C ) ))).
% 12.52/12.71  thf('182', plain,
% 12.52/12.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 12.52/12.71         (~ (r2_hidden @ X19 @ X20)
% 12.52/12.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 12.52/12.71          | (m1_subset_1 @ X19 @ X21))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset])).
% 12.52/12.71  thf('183', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['181', '182'])).
% 12.52/12.71  thf('184', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 12.52/12.71          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 12.52/12.71      inference('clc', [status(thm)], ['180', '183'])).
% 12.52/12.71  thf('185', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf(l3_subset_1, axiom,
% 12.52/12.71    (![A:$i,B:$i]:
% 12.52/12.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 12.52/12.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 12.52/12.71  thf('186', plain,
% 12.52/12.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 12.52/12.71         (~ (r2_hidden @ X15 @ X16)
% 12.52/12.71          | (r2_hidden @ X15 @ X17)
% 12.52/12.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 12.52/12.71      inference('cnf', [status(esa)], [l3_subset_1])).
% 12.52/12.71  thf('187', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['185', '186'])).
% 12.52/12.71  thf('188', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 12.52/12.71      inference('clc', [status(thm)], ['184', '187'])).
% 12.52/12.71  thf('189', plain,
% 12.52/12.71      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('clc', [status(thm)], ['123', '188'])).
% 12.52/12.71  thf('190', plain,
% 12.52/12.71      (((v1_tops_1 @ sk_B @ sk_A)
% 12.52/12.71        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 12.52/12.71      inference('demod', [status(thm)], ['50', '51'])).
% 12.52/12.71  thf('191', plain,
% 12.52/12.71      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 12.52/12.71         | (v1_tops_1 @ sk_B @ sk_A)))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['189', '190'])).
% 12.52/12.71  thf('192', plain,
% 12.52/12.71      (((v1_tops_1 @ sk_B @ sk_A))
% 12.52/12.71         <= ((![X46 : $i]:
% 12.52/12.71                (((X46) = (k1_xboole_0))
% 12.52/12.71                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['191'])).
% 12.52/12.71  thf('193', plain,
% 12.52/12.71      (((r1_xboole_0 @ sk_B @ sk_C) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('194', plain,
% 12.52/12.71      ((~ (v1_tops_1 @ sk_B @ sk_A)) <= (~ ((v1_tops_1 @ sk_B @ sk_A)))),
% 12.52/12.71      inference('split', [status(esa)], ['193'])).
% 12.52/12.71  thf('195', plain,
% 12.52/12.71      (~
% 12.52/12.71       (![X46 : $i]:
% 12.52/12.71          (((X46) = (k1_xboole_0))
% 12.52/12.71           | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71           | ~ (v3_pre_topc @ X46 @ sk_A)
% 12.52/12.71           | ~ (r1_xboole_0 @ sk_B @ X46))) | 
% 12.52/12.71       ((v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('sup-', [status(thm)], ['192', '194'])).
% 12.52/12.71  thf('196', plain,
% 12.52/12.71      (((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('split', [status(esa)], ['193'])).
% 12.52/12.71  thf('197', plain,
% 12.52/12.71      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('198', plain,
% 12.52/12.71      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('split', [status(esa)], ['197'])).
% 12.52/12.71  thf('199', plain,
% 12.52/12.71      ((((sk_C) != (k1_xboole_0)) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('200', plain,
% 12.52/12.71      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('split', [status(esa)], ['199'])).
% 12.52/12.71  thf('201', plain,
% 12.52/12.71      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('202', plain,
% 12.52/12.71      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 12.52/12.71       ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('split', [status(esa)], ['201'])).
% 12.52/12.71  thf('203', plain,
% 12.52/12.71      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('split', [status(esa)], ['201'])).
% 12.52/12.71  thf('204', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf('205', plain,
% 12.52/12.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ (u1_struct_0 @ X28))
% 12.52/12.71          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 12.52/12.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (l1_pre_topc @ X28))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.52/12.71  thf('206', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.52/12.71          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 12.52/12.71          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['204', '205'])).
% 12.52/12.71  thf('207', plain,
% 12.52/12.71      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.52/12.71         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 12.52/12.71         | ~ (l1_pre_topc @ sk_A)))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['203', '206'])).
% 12.52/12.71  thf('208', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['150', '151'])).
% 12.52/12.71  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('210', plain,
% 12.52/12.71      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.52/12.71         | ((sk_C) = (k1_xboole_0))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('demod', [status(thm)], ['207', '208', '209'])).
% 12.52/12.71  thf('211', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 12.52/12.71      inference('demod', [status(thm)], ['177', '178'])).
% 12.52/12.71  thf('212', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 12.52/12.71      inference('simplify', [status(thm)], ['161'])).
% 12.52/12.71  thf('213', plain,
% 12.52/12.71      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 12.52/12.71         ((zip_tseitin_0 @ X22 @ X24 @ X25 @ X26)
% 12.52/12.71          | ~ (r1_xboole_0 @ X25 @ X22)
% 12.52/12.71          | ~ (r2_hidden @ X24 @ X22)
% 12.52/12.71          | ~ (v3_pre_topc @ X22 @ X26))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.52/12.71  thf('214', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.52/12.71         (~ (v3_pre_topc @ X0 @ X1)
% 12.52/12.71          | ~ (r2_hidden @ X2 @ X0)
% 12.52/12.71          | (zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1))),
% 12.52/12.71      inference('sup-', [status(thm)], ['212', '213'])).
% 12.52/12.71  thf('215', plain,
% 12.52/12.71      (![X0 : $i]:
% 12.52/12.71         ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0 @ sk_A)
% 12.52/12.71          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['211', '214'])).
% 12.52/12.71  thf('216', plain,
% 12.52/12.71      (((((sk_C) = (k1_xboole_0))
% 12.52/12.71         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 12.52/12.71            (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['210', '215'])).
% 12.52/12.71  thf('217', plain,
% 12.52/12.71      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 12.52/12.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.71  thf('218', plain,
% 12.52/12.71      (![X27 : $i, X28 : $i, X29 : $i, X32 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ X29)
% 12.52/12.71          | ~ (zip_tseitin_0 @ X32 @ (sk_D @ X29 @ X27 @ X28) @ X27 @ X28)
% 12.52/12.71          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 12.52/12.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (l1_pre_topc @ X28))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.52/12.71  thf('219', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X0)
% 12.52/12.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.52/12.71          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 12.52/12.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.52/12.71          | ~ (zip_tseitin_0 @ X2 @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 12.52/12.71               k1_xboole_0 @ X0)
% 12.52/12.71          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 12.52/12.71      inference('sup-', [status(thm)], ['217', '218'])).
% 12.52/12.71  thf('220', plain,
% 12.52/12.71      (((((sk_C) = (k1_xboole_0))
% 12.52/12.71         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 12.52/12.71         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.52/12.71              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 12.52/12.71         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71         | ~ (l1_pre_topc @ sk_A)))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['216', '219'])).
% 12.52/12.71  thf('221', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('222', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 12.52/12.71      inference('demod', [status(thm)], ['150', '151'])).
% 12.52/12.71  thf('223', plain,
% 12.52/12.71      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('split', [status(esa)], ['201'])).
% 12.52/12.71  thf('224', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('225', plain,
% 12.52/12.71      (((((sk_C) = (k1_xboole_0))
% 12.52/12.71         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 12.52/12.71         | ((sk_C) = (k1_xboole_0))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('demod', [status(thm)], ['220', '221', '222', '223', '224'])).
% 12.52/12.71  thf('226', plain,
% 12.52/12.71      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 12.52/12.71         | ((sk_C) = (k1_xboole_0))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['225'])).
% 12.52/12.71  thf('227', plain,
% 12.52/12.71      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 12.52/12.71      inference('split', [status(esa)], ['197'])).
% 12.52/12.71  thf('228', plain,
% 12.52/12.71      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 12.52/12.71      inference('split', [status(esa)], ['193'])).
% 12.52/12.71  thf('229', plain,
% 12.52/12.71      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 12.52/12.71         ((zip_tseitin_0 @ X22 @ X24 @ X25 @ X26)
% 12.52/12.71          | ~ (r1_xboole_0 @ X25 @ X22)
% 12.52/12.71          | ~ (r2_hidden @ X24 @ X22)
% 12.52/12.71          | ~ (v3_pre_topc @ X22 @ X26))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.52/12.71  thf('230', plain,
% 12.52/12.71      ((![X0 : $i, X1 : $i]:
% 12.52/12.71          (~ (v3_pre_topc @ sk_C @ X0)
% 12.52/12.71           | ~ (r2_hidden @ X1 @ sk_C)
% 12.52/12.71           | (zip_tseitin_0 @ sk_C @ X1 @ sk_B @ X0)))
% 12.52/12.71         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['228', '229'])).
% 12.52/12.71  thf('231', plain,
% 12.52/12.71      ((![X0 : $i]:
% 12.52/12.71          ((zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A)
% 12.52/12.71           | ~ (r2_hidden @ X0 @ sk_C)))
% 12.52/12.71         <= (((r1_xboole_0 @ sk_B @ sk_C)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['227', '230'])).
% 12.52/12.71  thf('232', plain,
% 12.52/12.71      (((((sk_C) = (k1_xboole_0))
% 12.52/12.71         | (zip_tseitin_0 @ sk_C @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_B @ 
% 12.52/12.71            sk_A)))
% 12.52/12.71         <= (((r1_xboole_0 @ sk_B @ sk_C)) & 
% 12.52/12.71             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 12.52/12.71             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['226', '231'])).
% 12.52/12.71  thf('233', plain,
% 12.52/12.71      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('split', [status(esa)], ['201'])).
% 12.52/12.71  thf('234', plain,
% 12.52/12.71      (((v1_tops_1 @ sk_B @ sk_A)) <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 12.52/12.71      inference('split', [status(esa)], ['0'])).
% 12.52/12.71  thf('235', plain,
% 12.52/12.71      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 12.52/12.71        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 12.52/12.71      inference('demod', [status(thm)], ['62', '63'])).
% 12.52/12.71  thf('236', plain,
% 12.52/12.71      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 12.52/12.71         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['234', '235'])).
% 12.52/12.71  thf('237', plain,
% 12.52/12.71      (![X33 : $i]:
% 12.52/12.71         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.52/12.71  thf('238', plain,
% 12.52/12.71      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ((X29) != (k2_pre_topc @ X28 @ X27))
% 12.52/12.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (zip_tseitin_0 @ X30 @ X31 @ X27 @ X28)
% 12.52/12.71          | ~ (r2_hidden @ X31 @ X29)
% 12.52/12.71          | ~ (r2_hidden @ X31 @ (u1_struct_0 @ X28))
% 12.52/12.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (l1_pre_topc @ X28))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.52/12.71  thf('239', plain,
% 12.52/12.71      (![X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 12.52/12.71         (~ (l1_pre_topc @ X28)
% 12.52/12.71          | ~ (m1_subset_1 @ (k2_pre_topc @ X28 @ X27) @ 
% 12.52/12.71               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (r2_hidden @ X31 @ (u1_struct_0 @ X28))
% 12.52/12.71          | ~ (r2_hidden @ X31 @ (k2_pre_topc @ X28 @ X27))
% 12.52/12.71          | ~ (zip_tseitin_0 @ X30 @ X31 @ X27 @ X28)
% 12.52/12.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 12.52/12.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 12.52/12.71      inference('simplify', [status(thm)], ['238'])).
% 12.52/12.71  thf('240', plain,
% 12.52/12.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.52/12.71         (~ (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 12.52/12.71             (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 12.52/12.71          | ~ (l1_struct_0 @ X0)
% 12.52/12.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.52/12.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.52/12.71          | ~ (zip_tseitin_0 @ X2 @ X3 @ X1 @ X0)
% 12.52/12.71          | ~ (r2_hidden @ X3 @ (k2_pre_topc @ X0 @ X1))
% 12.52/12.71          | ~ (r2_hidden @ X3 @ (u1_struct_0 @ X0))
% 12.52/12.71          | ~ (l1_pre_topc @ X0))),
% 12.52/12.71      inference('sup-', [status(thm)], ['237', '239'])).
% 12.52/12.71  thf('241', plain,
% 12.52/12.71      ((![X0 : $i, X1 : $i]:
% 12.52/12.71          (~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 12.52/12.71              (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 12.52/12.71           | ~ (l1_pre_topc @ sk_A)
% 12.52/12.71           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 12.52/12.71           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 12.52/12.71           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 12.52/12.71           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.52/12.71           | ~ (l1_struct_0 @ sk_A)))
% 12.52/12.71         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['236', '240'])).
% 12.52/12.71  thf('242', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 12.52/12.71      inference('demod', [status(thm)], ['2', '3'])).
% 12.52/12.71  thf('243', plain, ((l1_pre_topc @ sk_A)),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('244', plain,
% 12.52/12.71      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 12.52/12.71         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 12.52/12.71      inference('sup-', [status(thm)], ['234', '235'])).
% 12.52/12.71  thf('245', plain,
% 12.52/12.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.52/12.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.71  thf('246', plain, ((l1_struct_0 @ sk_A)),
% 12.52/12.71      inference('sup-', [status(thm)], ['55', '56'])).
% 12.52/12.71  thf('247', plain,
% 12.52/12.71      ((![X0 : $i, X1 : $i]:
% 12.52/12.71          (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 12.52/12.71           | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 12.52/12.71           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 12.52/12.71           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 12.52/12.71         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 12.52/12.71      inference('demod', [status(thm)],
% 12.52/12.71                ['241', '242', '243', '244', '245', '246'])).
% 12.52/12.71  thf('248', plain,
% 12.52/12.71      ((![X0 : $i]:
% 12.52/12.71          (~ (zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A)
% 12.52/12.71           | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 12.52/12.71           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))))
% 12.52/12.71         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 12.52/12.71             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['233', '247'])).
% 12.52/12.71  thf('249', plain,
% 12.52/12.71      (((((sk_C) = (k1_xboole_0))
% 12.52/12.71         | ~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 12.52/12.71              (u1_struct_0 @ sk_A))
% 12.52/12.71         | ~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 12.52/12.71              (k2_struct_0 @ sk_A))))
% 12.52/12.71         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 12.52/12.71             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 12.52/12.71             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 12.52/12.71             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['232', '248'])).
% 12.52/12.71  thf('250', plain,
% 12.52/12.71      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.52/12.71         | ((sk_C) = (k1_xboole_0))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('demod', [status(thm)], ['207', '208', '209'])).
% 12.52/12.71  thf('251', plain,
% 12.52/12.71      (((~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 12.52/12.71            (k2_struct_0 @ sk_A))
% 12.52/12.71         | ((sk_C) = (k1_xboole_0))))
% 12.52/12.71         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 12.52/12.71             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 12.52/12.71             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 12.52/12.71             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('clc', [status(thm)], ['249', '250'])).
% 12.52/12.71  thf('252', plain,
% 12.52/12.71      (![X33 : $i]:
% 12.52/12.71         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 12.52/12.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.52/12.71  thf('253', plain,
% 12.52/12.71      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.52/12.71         | ((sk_C) = (k1_xboole_0))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('demod', [status(thm)], ['207', '208', '209'])).
% 12.52/12.71  thf('254', plain,
% 12.52/12.71      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 12.52/12.71         | ~ (l1_struct_0 @ sk_A)
% 12.52/12.71         | ((sk_C) = (k1_xboole_0))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('sup+', [status(thm)], ['252', '253'])).
% 12.52/12.71  thf('255', plain, ((l1_struct_0 @ sk_A)),
% 12.52/12.71      inference('sup-', [status(thm)], ['55', '56'])).
% 12.52/12.71  thf('256', plain,
% 12.52/12.71      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 12.52/12.71         | ((sk_C) = (k1_xboole_0))))
% 12.52/12.71         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('demod', [status(thm)], ['254', '255'])).
% 12.52/12.71  thf('257', plain,
% 12.52/12.71      ((((sk_C) = (k1_xboole_0)))
% 12.52/12.71         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 12.52/12.71             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 12.52/12.71             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 12.52/12.71             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('clc', [status(thm)], ['251', '256'])).
% 12.52/12.71  thf('258', plain,
% 12.52/12.71      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 12.52/12.71      inference('split', [status(esa)], ['199'])).
% 12.52/12.71  thf('259', plain,
% 12.52/12.71      ((((sk_C) != (sk_C)))
% 12.52/12.71         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 12.52/12.71             ((v1_tops_1 @ sk_B @ sk_A)) & 
% 12.52/12.71             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 12.52/12.71             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 12.52/12.71             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 12.52/12.71      inference('sup-', [status(thm)], ['257', '258'])).
% 12.52/12.71  thf('260', plain,
% 12.52/12.71      (~ ((v1_tops_1 @ sk_B @ sk_A)) | 
% 12.52/12.71       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 12.52/12.71       ~ ((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 12.52/12.71       (((sk_C) = (k1_xboole_0)))),
% 12.52/12.71      inference('simplify', [status(thm)], ['259'])).
% 12.52/12.71  thf('261', plain, ($false),
% 12.52/12.71      inference('sat_resolution*', [status(thm)],
% 12.52/12.71                ['1', '195', '196', '198', '200', '202', '260'])).
% 12.52/12.71  
% 12.52/12.71  % SZS output end Refutation
% 12.52/12.71  
% 12.52/12.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
