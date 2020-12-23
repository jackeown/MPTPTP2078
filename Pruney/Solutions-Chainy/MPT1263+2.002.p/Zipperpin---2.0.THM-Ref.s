%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YkGN0QK5an

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:05 EST 2020

% Result     : Theorem 7.66s
% Output     : Refutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  423 (14930 expanded)
%              Number of leaves         :   49 (4639 expanded)
%              Depth                    :   52
%              Number of atoms          : 5435 (173030 expanded)
%              Number of equality atoms :  279 (8668 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('14',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ X29 )
      | ( zip_tseitin_0 @ ( sk_E @ X29 @ X27 @ X28 ) @ ( sk_D @ X29 @ X27 @ X28 ) @ X27 @ X28 )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X2
        = ( k2_pre_topc @ X0 @ X1 ) )
      | ( zip_tseitin_0 @ ( sk_E @ X2 @ X1 @ X0 ) @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('35',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('39',plain,(
    ! [X43: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('40',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('42',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('47',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('54',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('60',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('66',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('67',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v4_pre_topc @ X44 @ X45 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('74',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('76',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X25 @ X22 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( v3_pre_topc @ X22 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v3_pre_topc @ X22 @ X23 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('90',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('97',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('99',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('100',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v2_pre_topc @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
       != X35 )
      | ( v4_pre_topc @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['97','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('109',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('118',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('120',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('125',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('126',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('127',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ X29 )
      | ( zip_tseitin_0 @ ( sk_E @ X29 @ X27 @ X28 ) @ ( sk_D @ X29 @ X27 @ X28 ) @ X27 @ X28 )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( zip_tseitin_0 @ ( sk_E @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('135',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X25 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('140',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_xboole_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('146',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( k5_xboole_0 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('149',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('155',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('156',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ X29 )
      | ( m1_subset_1 @ ( sk_E @ X29 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('165',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ X45 )
      | ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('175',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k2_pre_topc @ X0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['173','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

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

thf('181',plain,(
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

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['179','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','185'])).

thf('187',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['133','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['122','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('198',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['109','110'])).

thf('199',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['194','195','196','197','198'])).

thf('200',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('202',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v2_pre_topc @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
       != X35 )
      | ( v4_pre_topc @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['200','203'])).

thf('205',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,(
    v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','208'])).

thf('210',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('211',plain,(
    v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('213',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('214',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = X1 )
      | ~ ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['212','215'])).

thf('217',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','216'])).

thf('218',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('219',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('221',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('222',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('224',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['217','218','219','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','225'])).

thf('227',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','226'])).

thf('228',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('229',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( zip_tseitin_0 @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X25 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('232',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ sk_B @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('234',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('236',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X29 @ X27 @ X28 ) @ X29 )
      | ( m1_subset_1 @ ( sk_E @ X29 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X29
        = ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['236','241'])).

thf('243',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('244',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,
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

thf('247',plain,
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
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,
    ( ( ~ ( r1_xboole_0 @ sk_B @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
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
    inference('sup-',[status(thm)],['233','247'])).

thf('249',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('250',plain,
    ( ( ~ ( r1_xboole_0 @ sk_B @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) )
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
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['232','250'])).

thf('252',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['217','218','219','224'])).

thf('253',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['217','218','219','224'])).

thf('254',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['217','218','219','224'])).

thf('255',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('256',plain,
    ( ( ( ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v3_pre_topc @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ( zip_tseitin_0 @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('258',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v3_pre_topc @ X22 @ X23 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('259',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(clc,[status(thm)],['256','259'])).

thf('261',plain,
    ( ( zip_tseitin_0 @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('262',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('263',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_E @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,
    ( ( ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ k1_xboole_0 )
      | ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup+',[status(thm)],['260','263'])).

thf('265',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['97','106'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('268',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('272',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('273',plain,(
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

thf('274',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('276',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['271','276'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['270','277'])).

thf('279',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['109','110'])).

thf('282',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['280','281'])).

thf('283',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('284',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('285',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['282','285'])).

thf('287',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('288',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('289',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['286','289'])).

thf('291',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(clc,[status(thm)],['265','290'])).

thf('292',plain,(
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

thf('293',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_pre_topc @ X42 @ X41 )
       != ( k2_struct_0 @ X42 ) )
      | ( v1_tops_1 @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('294',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('297',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference('sup-',[status(thm)],['291','296'])).

thf('298',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ! [X46: $i] :
        ( ( X46 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X46 @ sk_A )
        | ~ ( r1_xboole_0 @ sk_B @ X46 ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['299'])).

thf('301',plain,
    ( ~ ! [X46: $i] :
          ( ( X46 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X46 @ sk_A )
          | ~ ( r1_xboole_0 @ sk_B @ X46 ) )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['298','300'])).

thf('302',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['299'])).

thf('303',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['303'])).

thf('305',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['305'])).

thf('307',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['307'])).

thf('309',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['307'])).

thf('310',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('311',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('315',plain,
    ( ( ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['268','269'])).

thf('317',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('318',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('319',plain,(
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

thf('320',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C
        = ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['317','320'])).

thf('322',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('323',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['268','269'])).

thf('324',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['307'])).

thf('325',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['321','322','323','324','325'])).

thf('327',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['303'])).

thf('329',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['299'])).

thf('330',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X25 @ X22 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( v3_pre_topc @ X22 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('331',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v3_pre_topc @ sk_C @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_C )
        | ( zip_tseitin_0 @ sk_C @ X1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['328','331'])).

thf('333',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_B @ sk_A ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['327','332'])).

thf('334',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['307'])).

thf('335',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('336',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v1_tops_1 @ X41 @ X42 )
      | ( ( k2_pre_topc @ X42 @ X41 )
        = ( k2_struct_0 @ X42 ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('338',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['336','337'])).

thf('339',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['338','339'])).

thf('341',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['335','340'])).

thf('342',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('343',plain,(
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

thf('344',plain,(
    ! [X27: $i,X28: $i,X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X28 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ X31 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_hidden @ X31 @ ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['343'])).

thf('345',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_pre_topc @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['342','344'])).

thf('346',plain,
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
    inference('sup-',[status(thm)],['341','345'])).

thf('347',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('348',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['335','340'])).

thf('350',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('352',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['346','347','348','349','350','351'])).

thf('353',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['334','352'])).

thf('354',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['333','353'])).

thf('355',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('356',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('357',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['355','356'])).

thf('358',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['354','357'])).

thf('359',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['326'])).

thf('360',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('361',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['307'])).

thf('362',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['360','361'])).

thf('363',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('364',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['362','363'])).

thf('365',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('366',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['359','366'])).

thf('368',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['358','367'])).

thf('369',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['305'])).

thf('370',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v1_tops_1 @ sk_B @ sk_A )
      & ( r1_xboole_0 @ sk_B @ sk_C )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['368','369'])).

thf('371',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','301','302','304','306','308','371'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YkGN0QK5an
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:18:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.66/7.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.66/7.87  % Solved by: fo/fo7.sh
% 7.66/7.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.66/7.87  % done 15143 iterations in 7.405s
% 7.66/7.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.66/7.87  % SZS output start Refutation
% 7.66/7.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.66/7.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.66/7.87  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 7.66/7.87  thf(sk_A_type, type, sk_A: $i).
% 7.66/7.87  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 7.66/7.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.66/7.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.66/7.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 7.66/7.87  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.66/7.87  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 7.66/7.87  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 7.66/7.87  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 7.66/7.87  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 7.66/7.87  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.66/7.87  thf(sk_B_type, type, sk_B: $i).
% 7.66/7.87  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 7.66/7.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.66/7.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.66/7.87  thf(sk_C_type, type, sk_C: $i).
% 7.66/7.87  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 7.66/7.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.66/7.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.66/7.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.66/7.87  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.66/7.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.66/7.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.66/7.87  thf(t80_tops_1, conjecture,
% 7.66/7.87    (![A:$i]:
% 7.66/7.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.66/7.87       ( ![B:$i]:
% 7.66/7.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87           ( ( v1_tops_1 @ B @ A ) <=>
% 7.66/7.87             ( ![C:$i]:
% 7.66/7.87               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87                 ( ~( ( ( C ) != ( k1_xboole_0 ) ) & ( v3_pre_topc @ C @ A ) & 
% 7.66/7.87                      ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ))).
% 7.66/7.87  thf(zf_stmt_0, negated_conjecture,
% 7.66/7.87    (~( ![A:$i]:
% 7.66/7.87        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.66/7.87          ( ![B:$i]:
% 7.66/7.87            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87              ( ( v1_tops_1 @ B @ A ) <=>
% 7.66/7.87                ( ![C:$i]:
% 7.66/7.87                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87                    ( ~( ( ( C ) != ( k1_xboole_0 ) ) & 
% 7.66/7.87                         ( v3_pre_topc @ C @ A ) & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ) )),
% 7.66/7.87    inference('cnf.neg', [status(esa)], [t80_tops_1])).
% 7.66/7.87  thf('0', plain,
% 7.66/7.87      (![X46 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ((X46) = (k1_xboole_0))
% 7.66/7.87          | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.87          | ~ (r1_xboole_0 @ sk_B @ X46)
% 7.66/7.87          | (v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('1', plain,
% 7.66/7.87      ((![X46 : $i]:
% 7.66/7.87          (((X46) = (k1_xboole_0))
% 7.66/7.87           | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87           | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.87           | ~ (r1_xboole_0 @ sk_B @ X46))) | 
% 7.66/7.87       ((v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.87      inference('split', [status(esa)], ['0'])).
% 7.66/7.87  thf(d3_struct_0, axiom,
% 7.66/7.87    (![A:$i]:
% 7.66/7.87     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 7.66/7.87  thf('2', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf(dt_k2_subset_1, axiom,
% 7.66/7.87    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 7.66/7.87  thf('3', plain,
% 7.66/7.87      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 7.66/7.87  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 7.66/7.87  thf('4', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 7.66/7.87      inference('cnf', [status(esa)], [d4_subset_1])).
% 7.66/7.87  thf('5', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('6', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf('7', plain,
% 7.66/7.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf(d13_pre_topc, axiom,
% 7.66/7.87    (![A:$i]:
% 7.66/7.87     ( ( l1_pre_topc @ A ) =>
% 7.66/7.87       ( ![B:$i]:
% 7.66/7.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87           ( ![C:$i]:
% 7.66/7.87             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 7.66/7.87                 ( ![D:$i]:
% 7.66/7.87                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 7.66/7.87                     ( ( r2_hidden @ D @ C ) <=>
% 7.66/7.87                       ( ![E:$i]:
% 7.66/7.87                         ( ( m1_subset_1 @
% 7.66/7.87                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87                           ( ~( ( r1_xboole_0 @ B @ E ) & 
% 7.66/7.87                                ( r2_hidden @ D @ E ) & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.66/7.87  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 7.66/7.87  thf(zf_stmt_2, axiom,
% 7.66/7.87    (![E:$i,D:$i,B:$i,A:$i]:
% 7.66/7.87     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 7.66/7.87       ( ( v3_pre_topc @ E @ A ) & ( r2_hidden @ D @ E ) & 
% 7.66/7.87         ( r1_xboole_0 @ B @ E ) ) ))).
% 7.66/7.87  thf(zf_stmt_3, axiom,
% 7.66/7.87    (![A:$i]:
% 7.66/7.87     ( ( l1_pre_topc @ A ) =>
% 7.66/7.87       ( ![B:$i]:
% 7.66/7.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87           ( ![C:$i]:
% 7.66/7.87             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87               ( ( ( C ) = ( k2_pre_topc @ A @ B ) ) <=>
% 7.66/7.87                 ( ![D:$i]:
% 7.66/7.87                   ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) ) =>
% 7.66/7.87                     ( ( r2_hidden @ D @ C ) <=>
% 7.66/7.87                       ( ![E:$i]:
% 7.66/7.87                         ( ( m1_subset_1 @
% 7.66/7.87                             E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87                           ( ~( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.66/7.87  thf('8', plain,
% 7.66/7.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ (u1_struct_0 @ X28))
% 7.66/7.87          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 7.66/7.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (l1_pre_topc @ X28))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.87  thf('9', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ sk_A)
% 7.66/7.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['7', '8'])).
% 7.66/7.87  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('11', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('demod', [status(thm)], ['9', '10'])).
% 7.66/7.87  thf('12', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.66/7.87          | ~ (l1_struct_0 @ sk_A)
% 7.66/7.87          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['6', '11'])).
% 7.66/7.87  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf(dt_l1_pre_topc, axiom,
% 7.66/7.87    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 7.66/7.87  thf('14', plain,
% 7.66/7.87      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 7.66/7.87      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 7.66/7.87  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('16', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.87      inference('demod', [status(thm)], ['12', '15'])).
% 7.66/7.87  thf('17', plain,
% 7.66/7.87      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87        | (r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.87           (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['5', '16'])).
% 7.66/7.87  thf('18', plain,
% 7.66/7.87      (((r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.87         (k2_struct_0 @ sk_A))
% 7.66/7.87        | ~ (l1_struct_0 @ sk_A)
% 7.66/7.87        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.87      inference('sup+', [status(thm)], ['2', '17'])).
% 7.66/7.87  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('20', plain,
% 7.66/7.87      (((r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.87         (k2_struct_0 @ sk_A))
% 7.66/7.87        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.87      inference('demod', [status(thm)], ['18', '19'])).
% 7.66/7.87  thf('21', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf('22', plain,
% 7.66/7.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('23', plain,
% 7.66/7.87      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.66/7.87        | ~ (l1_struct_0 @ sk_A))),
% 7.66/7.87      inference('sup+', [status(thm)], ['21', '22'])).
% 7.66/7.87  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('25', plain,
% 7.66/7.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.66/7.87      inference('demod', [status(thm)], ['23', '24'])).
% 7.66/7.87  thf('26', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf('27', plain,
% 7.66/7.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ X29)
% 7.66/7.87          | (zip_tseitin_0 @ (sk_E @ X29 @ X27 @ X28) @ 
% 7.66/7.87             (sk_D @ X29 @ X27 @ X28) @ X27 @ X28)
% 7.66/7.87          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 7.66/7.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (l1_pre_topc @ X28))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.87  thf('28', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((X2) = (k2_pre_topc @ X0 @ X1))
% 7.66/7.87          | (zip_tseitin_0 @ (sk_E @ X2 @ X1 @ X0) @ (sk_D @ X2 @ X1 @ X0) @ 
% 7.66/7.87             X1 @ X0)
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2))),
% 7.66/7.87      inference('sup-', [status(thm)], ['26', '27'])).
% 7.66/7.87  thf('29', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 7.66/7.87          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 7.66/7.87             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ~ (l1_pre_topc @ sk_A)
% 7.66/7.87          | ~ (l1_struct_0 @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['25', '28'])).
% 7.66/7.87  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('32', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 7.66/7.87          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 7.66/7.87             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.66/7.87      inference('demod', [status(thm)], ['29', '30', '31'])).
% 7.66/7.87  thf('33', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf('34', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('35', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('36', plain,
% 7.66/7.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ (u1_struct_0 @ X28))
% 7.66/7.87          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 7.66/7.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (l1_pre_topc @ X28))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.87  thf('37', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((X1) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X1 @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (u1_struct_0 @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['35', '36'])).
% 7.66/7.87  thf('38', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((r2_hidden @ (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (u1_struct_0 @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['34', '37'])).
% 7.66/7.87  thf(fc10_tops_1, axiom,
% 7.66/7.87    (![A:$i]:
% 7.66/7.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.66/7.87       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 7.66/7.87  thf('39', plain,
% 7.66/7.87      (![X43 : $i]:
% 7.66/7.87         ((v3_pre_topc @ (k2_struct_0 @ X43) @ X43)
% 7.66/7.87          | ~ (l1_pre_topc @ X43)
% 7.66/7.87          | ~ (v2_pre_topc @ X43))),
% 7.66/7.87      inference('cnf', [status(esa)], [fc10_tops_1])).
% 7.66/7.87  thf('40', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf(t4_subset_1, axiom,
% 7.66/7.87    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 7.66/7.87  thf('41', plain,
% 7.66/7.87      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.87  thf(t29_tops_1, axiom,
% 7.66/7.87    (![A:$i]:
% 7.66/7.87     ( ( l1_pre_topc @ A ) =>
% 7.66/7.87       ( ![B:$i]:
% 7.66/7.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87           ( ( v4_pre_topc @ B @ A ) <=>
% 7.66/7.87             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 7.66/7.87  thf('42', plain,
% 7.66/7.87      (![X44 : $i, X45 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.66/7.87          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 7.66/7.87          | (v4_pre_topc @ X44 @ X45)
% 7.66/7.87          | ~ (l1_pre_topc @ X45))),
% 7.66/7.87      inference('cnf', [status(esa)], [t29_tops_1])).
% 7.66/7.87  thf('43', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.66/7.87          | ~ (v3_pre_topc @ 
% 7.66/7.87               (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['41', '42'])).
% 7.66/7.87  thf('44', plain,
% 7.66/7.87      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.87  thf(d5_subset_1, axiom,
% 7.66/7.87    (![A:$i,B:$i]:
% 7.66/7.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.66/7.87       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 7.66/7.87  thf('45', plain,
% 7.66/7.87      (![X10 : $i, X11 : $i]:
% 7.66/7.87         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 7.66/7.87          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 7.66/7.87      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.66/7.87  thf('46', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['44', '45'])).
% 7.66/7.87  thf(t3_boole, axiom,
% 7.66/7.87    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.66/7.87  thf('47', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 7.66/7.87      inference('cnf', [status(esa)], [t3_boole])).
% 7.66/7.87  thf('48', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 7.66/7.87      inference('demod', [status(thm)], ['46', '47'])).
% 7.66/7.87  thf('49', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 7.66/7.87      inference('demod', [status(thm)], ['43', '48'])).
% 7.66/7.87  thf('50', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['40', '49'])).
% 7.66/7.87  thf('51', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['39', '50'])).
% 7.66/7.87  thf('52', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_struct_0 @ X0)
% 7.66/7.87          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['51'])).
% 7.66/7.87  thf('53', plain,
% 7.66/7.87      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.87  thf(t52_pre_topc, axiom,
% 7.66/7.87    (![A:$i]:
% 7.66/7.87     ( ( l1_pre_topc @ A ) =>
% 7.66/7.87       ( ![B:$i]:
% 7.66/7.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 7.66/7.87             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 7.66/7.87               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 7.66/7.87  thf('54', plain,
% 7.66/7.87      (![X35 : $i, X36 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.66/7.87          | ~ (v4_pre_topc @ X35 @ X36)
% 7.66/7.87          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 7.66/7.87          | ~ (l1_pre_topc @ X36))),
% 7.66/7.87      inference('cnf', [status(esa)], [t52_pre_topc])).
% 7.66/7.87  thf('55', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 7.66/7.87          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['53', '54'])).
% 7.66/7.87  thf('56', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['52', '55'])).
% 7.66/7.87  thf('57', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['56'])).
% 7.66/7.87  thf('58', plain,
% 7.66/7.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('59', plain,
% 7.66/7.87      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.87  thf('60', plain,
% 7.66/7.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ (u1_struct_0 @ X28))
% 7.66/7.87          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 7.66/7.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (l1_pre_topc @ X28))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.87  thf('61', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['59', '60'])).
% 7.66/7.87  thf('62', plain,
% 7.66/7.87      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.66/7.87        | ((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.87        | ~ (l1_pre_topc @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['58', '61'])).
% 7.66/7.87  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('64', plain,
% 7.66/7.87      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.66/7.87        | ((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0)))),
% 7.66/7.87      inference('demod', [status(thm)], ['62', '63'])).
% 7.66/7.87  thf('65', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_struct_0 @ X0)
% 7.66/7.87          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['51'])).
% 7.66/7.87  thf('66', plain,
% 7.66/7.87      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.87  thf('67', plain,
% 7.66/7.87      (![X44 : $i, X45 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.66/7.87          | ~ (v4_pre_topc @ X44 @ X45)
% 7.66/7.87          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 7.66/7.87          | ~ (l1_pre_topc @ X45))),
% 7.66/7.87      inference('cnf', [status(esa)], [t29_tops_1])).
% 7.66/7.87  thf('68', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 7.66/7.87             X0)
% 7.66/7.87          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['66', '67'])).
% 7.66/7.87  thf('69', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 7.66/7.87      inference('demod', [status(thm)], ['46', '47'])).
% 7.66/7.87  thf('70', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 7.66/7.87      inference('demod', [status(thm)], ['68', '69'])).
% 7.66/7.87  thf('71', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['65', '70'])).
% 7.66/7.87  thf('72', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['71'])).
% 7.66/7.87  thf(commutativity_k3_xboole_0, axiom,
% 7.66/7.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.66/7.87  thf('73', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.66/7.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.66/7.87  thf(t2_boole, axiom,
% 7.66/7.87    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 7.66/7.87  thf('74', plain,
% 7.66/7.87      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 7.66/7.87      inference('cnf', [status(esa)], [t2_boole])).
% 7.66/7.87  thf('75', plain,
% 7.66/7.87      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 7.66/7.87      inference('sup+', [status(thm)], ['73', '74'])).
% 7.66/7.87  thf(d7_xboole_0, axiom,
% 7.66/7.87    (![A:$i,B:$i]:
% 7.66/7.87     ( ( r1_xboole_0 @ A @ B ) <=>
% 7.66/7.87       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 7.66/7.87  thf('76', plain,
% 7.66/7.87      (![X2 : $i, X4 : $i]:
% 7.66/7.87         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 7.66/7.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 7.66/7.87  thf('77', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['75', '76'])).
% 7.66/7.87  thf('78', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 7.66/7.87      inference('simplify', [status(thm)], ['77'])).
% 7.66/7.87  thf('79', plain,
% 7.66/7.87      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 7.66/7.87         ((zip_tseitin_0 @ X22 @ X24 @ X25 @ X26)
% 7.66/7.87          | ~ (r1_xboole_0 @ X25 @ X22)
% 7.66/7.87          | ~ (r2_hidden @ X24 @ X22)
% 7.66/7.87          | ~ (v3_pre_topc @ X22 @ X26))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.87  thf('80', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.87         (~ (v3_pre_topc @ X0 @ X1)
% 7.66/7.87          | ~ (r2_hidden @ X2 @ X0)
% 7.66/7.87          | (zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1))),
% 7.66/7.87      inference('sup-', [status(thm)], ['78', '79'])).
% 7.66/7.87  thf('81', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ k1_xboole_0 @ X0)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['72', '80'])).
% 7.66/7.87  thf('82', plain,
% 7.66/7.87      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.87        | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.87           (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)
% 7.66/7.87        | ~ (l1_struct_0 @ sk_A)
% 7.66/7.87        | ~ (l1_pre_topc @ sk_A)
% 7.66/7.87        | ~ (v2_pre_topc @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['64', '81'])).
% 7.66/7.87  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('86', plain,
% 7.66/7.87      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.87        | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.87           (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 7.66/7.87  thf('87', plain,
% 7.66/7.87      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.66/7.87         ((v3_pre_topc @ X22 @ X23) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.87  thf('88', plain,
% 7.66/7.87      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.87        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['86', '87'])).
% 7.66/7.87  thf('89', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 7.66/7.87      inference('demod', [status(thm)], ['43', '48'])).
% 7.66/7.87  thf('90', plain,
% 7.66/7.87      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.87        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 7.66/7.87        | ~ (l1_pre_topc @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['88', '89'])).
% 7.66/7.87  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('92', plain,
% 7.66/7.87      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.87        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['90', '91'])).
% 7.66/7.87  thf('93', plain,
% 7.66/7.87      ((((sk_B) = (k1_xboole_0))
% 7.66/7.87        | ~ (v2_pre_topc @ sk_A)
% 7.66/7.87        | ~ (l1_pre_topc @ sk_A)
% 7.66/7.87        | ~ (l1_struct_0 @ sk_A)
% 7.66/7.87        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 7.66/7.87      inference('sup+', [status(thm)], ['57', '92'])).
% 7.66/7.87  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('97', plain,
% 7.66/7.87      ((((sk_B) = (k1_xboole_0)) | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 7.66/7.87  thf('98', plain,
% 7.66/7.87      ((((sk_B) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.87        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['90', '91'])).
% 7.66/7.87  thf('99', plain,
% 7.66/7.87      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.87  thf('100', plain,
% 7.66/7.87      (![X35 : $i, X36 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.66/7.87          | ~ (v2_pre_topc @ X36)
% 7.66/7.87          | ((k2_pre_topc @ X36 @ X35) != (X35))
% 7.66/7.87          | (v4_pre_topc @ X35 @ X36)
% 7.66/7.87          | ~ (l1_pre_topc @ X36))),
% 7.66/7.87      inference('cnf', [status(esa)], [t52_pre_topc])).
% 7.66/7.87  thf('101', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.66/7.87          | ((k2_pre_topc @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['99', '100'])).
% 7.66/7.87  thf('102', plain,
% 7.66/7.87      ((((sk_B) != (k1_xboole_0))
% 7.66/7.87        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 7.66/7.87        | ~ (v2_pre_topc @ sk_A)
% 7.66/7.87        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 7.66/7.87        | ~ (l1_pre_topc @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['98', '101'])).
% 7.66/7.87  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('105', plain,
% 7.66/7.87      ((((sk_B) != (k1_xboole_0))
% 7.66/7.87        | (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 7.66/7.87        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['102', '103', '104'])).
% 7.66/7.87  thf('106', plain,
% 7.66/7.87      (((v4_pre_topc @ k1_xboole_0 @ sk_A) | ((sk_B) != (k1_xboole_0)))),
% 7.66/7.87      inference('simplify', [status(thm)], ['105'])).
% 7.66/7.87  thf('107', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 7.66/7.87      inference('clc', [status(thm)], ['97', '106'])).
% 7.66/7.87  thf('108', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 7.66/7.87      inference('demod', [status(thm)], ['68', '69'])).
% 7.66/7.87  thf('109', plain,
% 7.66/7.87      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['107', '108'])).
% 7.66/7.87  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('111', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 7.66/7.87      inference('demod', [status(thm)], ['109', '110'])).
% 7.66/7.87  thf('112', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.87         (~ (v3_pre_topc @ X0 @ X1)
% 7.66/7.87          | ~ (r2_hidden @ X2 @ X0)
% 7.66/7.87          | (zip_tseitin_0 @ X0 @ X2 @ k1_xboole_0 @ X1))),
% 7.66/7.87      inference('sup-', [status(thm)], ['78', '79'])).
% 7.66/7.87  thf('113', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0 @ sk_A)
% 7.66/7.87          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['111', '112'])).
% 7.66/7.87  thf('114', plain,
% 7.66/7.87      ((~ (l1_pre_topc @ sk_A)
% 7.66/7.87        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 7.66/7.87        | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.87           (sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_A) @ 
% 7.66/7.87           k1_xboole_0 @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['38', '113'])).
% 7.66/7.87  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('116', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 7.66/7.87        | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.87           (sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_A) @ 
% 7.66/7.87           k1_xboole_0 @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['114', '115'])).
% 7.66/7.87  thf('117', plain,
% 7.66/7.87      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.66/7.87         ((r2_hidden @ X24 @ X22) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.87  thf('118', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 7.66/7.87        | (r2_hidden @ 
% 7.66/7.87           (sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_A) @ 
% 7.66/7.87           (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['116', '117'])).
% 7.66/7.87  thf('119', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf(t4_subset, axiom,
% 7.66/7.87    (![A:$i,B:$i,C:$i]:
% 7.66/7.87     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 7.66/7.87       ( m1_subset_1 @ A @ C ) ))).
% 7.66/7.87  thf('120', plain,
% 7.66/7.87      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.66/7.87         (~ (r2_hidden @ X19 @ X20)
% 7.66/7.87          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 7.66/7.87          | (m1_subset_1 @ X19 @ X21))),
% 7.66/7.87      inference('cnf', [status(esa)], [t4_subset])).
% 7.66/7.87  thf('121', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['119', '120'])).
% 7.66/7.87  thf('122', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 7.66/7.87        | (m1_subset_1 @ 
% 7.66/7.87           (sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_A) @ 
% 7.66/7.87           (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['118', '121'])).
% 7.66/7.87  thf('123', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((r2_hidden @ (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (u1_struct_0 @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['34', '37'])).
% 7.66/7.87  thf('124', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((r2_hidden @ (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (u1_struct_0 @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['34', '37'])).
% 7.66/7.87  thf('125', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('126', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('127', plain,
% 7.66/7.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ X29)
% 7.66/7.87          | (zip_tseitin_0 @ (sk_E @ X29 @ X27 @ X28) @ 
% 7.66/7.87             (sk_D @ X29 @ X27 @ X28) @ X27 @ X28)
% 7.66/7.87          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 7.66/7.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (l1_pre_topc @ X28))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.87  thf('128', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((X1) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (zip_tseitin_0 @ (sk_E @ X1 @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (sk_D @ X1 @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X1 @ (u1_struct_0 @ X0) @ X0) @ X1))),
% 7.66/7.87      inference('sup-', [status(thm)], ['126', '127'])).
% 7.66/7.87  thf('129', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (r2_hidden @ 
% 7.66/7.87             (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (u1_struct_0 @ X0))
% 7.66/7.87          | (zip_tseitin_0 @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['125', '128'])).
% 7.66/7.87  thf('130', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (zip_tseitin_0 @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (u1_struct_0 @ X0) @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['124', '129'])).
% 7.66/7.87  thf('131', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((zip_tseitin_0 @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['130'])).
% 7.66/7.87  thf('132', plain,
% 7.66/7.87      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.66/7.87         ((r2_hidden @ X24 @ X22) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.87  thf('133', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (r2_hidden @ 
% 7.66/7.87             (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['131', '132'])).
% 7.66/7.87  thf('134', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((zip_tseitin_0 @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['130'])).
% 7.66/7.87  thf('135', plain,
% 7.66/7.87      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.66/7.87         ((r1_xboole_0 @ X25 @ X22) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.87  thf('136', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (r1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['134', '135'])).
% 7.66/7.87  thf('137', plain,
% 7.66/7.87      (![X2 : $i, X3 : $i]:
% 7.66/7.87         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 7.66/7.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 7.66/7.87  thf('138', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((k3_xboole_0 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87              = (k1_xboole_0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['136', '137'])).
% 7.66/7.87  thf('139', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.66/7.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.66/7.87  thf('140', plain,
% 7.66/7.87      (![X2 : $i, X4 : $i]:
% 7.66/7.87         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 7.66/7.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 7.66/7.87  thf('141', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 7.66/7.87      inference('sup-', [status(thm)], ['139', '140'])).
% 7.66/7.87  thf('142', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((k1_xboole_0) != (k1_xboole_0))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (r1_xboole_0 @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (u1_struct_0 @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['138', '141'])).
% 7.66/7.87  thf('143', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((r1_xboole_0 @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (u1_struct_0 @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['142'])).
% 7.66/7.87  thf('144', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['71'])).
% 7.66/7.87  thf('145', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((k3_xboole_0 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87              = (k1_xboole_0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['136', '137'])).
% 7.66/7.87  thf(t100_xboole_1, axiom,
% 7.66/7.87    (![A:$i,B:$i]:
% 7.66/7.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.66/7.87  thf('146', plain,
% 7.66/7.87      (![X5 : $i, X6 : $i]:
% 7.66/7.87         ((k4_xboole_0 @ X5 @ X6)
% 7.66/7.87           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 7.66/7.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.66/7.87  thf('147', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87            (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87            = (k5_xboole_0 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 7.66/7.87      inference('sup+', [status(thm)], ['145', '146'])).
% 7.66/7.87  thf('148', plain,
% 7.66/7.87      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 7.66/7.87      inference('cnf', [status(esa)], [t2_boole])).
% 7.66/7.87  thf('149', plain,
% 7.66/7.87      (![X5 : $i, X6 : $i]:
% 7.66/7.87         ((k4_xboole_0 @ X5 @ X6)
% 7.66/7.87           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 7.66/7.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.66/7.87  thf('150', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.66/7.87      inference('sup+', [status(thm)], ['148', '149'])).
% 7.66/7.87  thf('151', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 7.66/7.87      inference('cnf', [status(esa)], [t3_boole])).
% 7.66/7.87  thf('152', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 7.66/7.87      inference('sup+', [status(thm)], ['150', '151'])).
% 7.66/7.87  thf('153', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87            (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87            = (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 7.66/7.87      inference('demod', [status(thm)], ['147', '152'])).
% 7.66/7.87  thf('154', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((r2_hidden @ (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (u1_struct_0 @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['34', '37'])).
% 7.66/7.87  thf('155', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('156', plain,
% 7.66/7.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ X29)
% 7.66/7.87          | (m1_subset_1 @ (sk_E @ X29 @ X27 @ X28) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 7.66/7.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (l1_pre_topc @ X28))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.87  thf('157', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((X1) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (m1_subset_1 @ (sk_E @ X1 @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X1 @ (u1_struct_0 @ X0) @ X0) @ X1))),
% 7.66/7.87      inference('sup-', [status(thm)], ['155', '156'])).
% 7.66/7.87  thf('158', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (m1_subset_1 @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87               (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['154', '157'])).
% 7.66/7.87  thf('159', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('160', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (m1_subset_1 @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('demod', [status(thm)], ['158', '159'])).
% 7.66/7.87  thf('161', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((m1_subset_1 @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['160'])).
% 7.66/7.87  thf('162', plain,
% 7.66/7.87      (![X10 : $i, X11 : $i]:
% 7.66/7.87         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 7.66/7.87          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 7.66/7.87      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.66/7.87  thf('163', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87                 (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))))),
% 7.66/7.87      inference('sup-', [status(thm)], ['161', '162'])).
% 7.66/7.87  thf('164', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((m1_subset_1 @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['160'])).
% 7.66/7.87  thf('165', plain,
% 7.66/7.87      (![X44 : $i, X45 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.66/7.87          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44) @ X45)
% 7.66/7.87          | (v4_pre_topc @ X44 @ X45)
% 7.66/7.87          | ~ (l1_pre_topc @ X45))),
% 7.66/7.87      inference('cnf', [status(esa)], [t29_tops_1])).
% 7.66/7.87  thf('166', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0)
% 7.66/7.87          | ~ (v3_pre_topc @ 
% 7.66/7.87               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87                (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)) @ 
% 7.66/7.87               X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['164', '165'])).
% 7.66/7.87  thf('167', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v3_pre_topc @ 
% 7.66/7.87             (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)) @ 
% 7.66/7.87             X0)
% 7.66/7.87          | (v4_pre_topc @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['166'])).
% 7.66/7.87  thf('168', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v3_pre_topc @ 
% 7.66/7.87             (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)) @ 
% 7.66/7.87             X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | (v4_pre_topc @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['163', '167'])).
% 7.66/7.87  thf('169', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((v4_pre_topc @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (v3_pre_topc @ 
% 7.66/7.87               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87                (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)) @ 
% 7.66/7.87               X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['168'])).
% 7.66/7.87  thf('170', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['153', '169'])).
% 7.66/7.87  thf('171', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((v4_pre_topc @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['170'])).
% 7.66/7.87  thf('172', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['144', '171'])).
% 7.66/7.87  thf('173', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((v4_pre_topc @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['172'])).
% 7.66/7.87  thf('174', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((m1_subset_1 @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['160'])).
% 7.66/7.87  thf('175', plain,
% 7.66/7.87      (![X35 : $i, X36 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.66/7.87          | ~ (v4_pre_topc @ X35 @ X36)
% 7.66/7.87          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 7.66/7.87          | ~ (l1_pre_topc @ X36))),
% 7.66/7.87      inference('cnf', [status(esa)], [t52_pre_topc])).
% 7.66/7.87  thf('176', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((k2_pre_topc @ X0 @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87              = (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87          | ~ (v4_pre_topc @ 
% 7.66/7.87               (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['174', '175'])).
% 7.66/7.87  thf('177', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v4_pre_topc @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X0)
% 7.66/7.87          | ((k2_pre_topc @ X0 @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87              = (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['176'])).
% 7.66/7.87  thf('178', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((k2_pre_topc @ X0 @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87              = (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['173', '177'])).
% 7.66/7.87  thf('179', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((k2_pre_topc @ X0 @ 
% 7.66/7.87            (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87            = (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['178'])).
% 7.66/7.87  thf('180', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         ((m1_subset_1 @ 
% 7.66/7.87           (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['160'])).
% 7.66/7.87  thf(t54_pre_topc, axiom,
% 7.66/7.87    (![A:$i]:
% 7.66/7.87     ( ( l1_pre_topc @ A ) =>
% 7.66/7.87       ( ![B:$i]:
% 7.66/7.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87           ( ![C:$i]:
% 7.66/7.87             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 7.66/7.87               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 7.66/7.87                 ( ( ~( v2_struct_0 @ A ) ) & 
% 7.66/7.87                   ( ![D:$i]:
% 7.66/7.87                     ( ( m1_subset_1 @
% 7.66/7.87                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.87                       ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 7.66/7.87                            ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.66/7.87  thf('181', plain,
% 7.66/7.87      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.66/7.87          | ~ (r2_hidden @ X39 @ (k2_pre_topc @ X38 @ X37))
% 7.66/7.87          | ~ (r1_xboole_0 @ X37 @ X40)
% 7.66/7.87          | ~ (r2_hidden @ X39 @ X40)
% 7.66/7.87          | ~ (v3_pre_topc @ X40 @ X38)
% 7.66/7.87          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.66/7.87          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 7.66/7.87          | ~ (l1_pre_topc @ X38))),
% 7.66/7.87      inference('cnf', [status(esa)], [t54_pre_topc])).
% 7.66/7.87  thf('182', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (v3_pre_topc @ X2 @ X0)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ X2)
% 7.66/7.87          | ~ (r1_xboole_0 @ 
% 7.66/7.87               (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X2)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ 
% 7.66/7.87               (k2_pre_topc @ X0 @ 
% 7.66/7.87                (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))))),
% 7.66/7.87      inference('sup-', [status(thm)], ['180', '181'])).
% 7.66/7.87  thf('183', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.87         (~ (r2_hidden @ X1 @ 
% 7.66/7.87             (k2_pre_topc @ X0 @ 
% 7.66/7.87              (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)))
% 7.66/7.87          | ~ (r1_xboole_0 @ 
% 7.66/7.87               (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X2)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ X2)
% 7.66/7.87          | ~ (v3_pre_topc @ X2 @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['182'])).
% 7.66/7.87  thf('184', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.87         (~ (r2_hidden @ X1 @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (v3_pre_topc @ X2 @ X0)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ X2)
% 7.66/7.87          | ~ (r1_xboole_0 @ 
% 7.66/7.87               (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X2))),
% 7.66/7.87      inference('sup-', [status(thm)], ['179', '183'])).
% 7.66/7.87  thf('185', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.87         (~ (r1_xboole_0 @ 
% 7.66/7.87             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ X2)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ X2)
% 7.66/7.87          | ~ (v3_pre_topc @ X2 @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ 
% 7.66/7.87               (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)))),
% 7.66/7.87      inference('simplify', [status(thm)], ['184'])).
% 7.66/7.87  thf('186', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (r2_hidden @ X1 @ 
% 7.66/7.87               (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 7.66/7.87               (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['143', '185'])).
% 7.66/7.87  thf('187', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('188', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (r2_hidden @ X1 @ 
% 7.66/7.87               (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 7.66/7.87      inference('demod', [status(thm)], ['186', '187'])).
% 7.66/7.87  thf('189', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (r2_hidden @ X1 @ 
% 7.66/7.87               (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['188'])).
% 7.66/7.87  thf('190', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ 
% 7.66/7.87               (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87               (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (r2_hidden @ 
% 7.66/7.87               (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87               (u1_struct_0 @ X0)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['133', '189'])).
% 7.66/7.87  thf('191', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (r2_hidden @ 
% 7.66/7.87             (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87             (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ 
% 7.66/7.87               (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87               (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 7.66/7.87      inference('simplify', [status(thm)], ['190'])).
% 7.66/7.87  thf('192', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ 
% 7.66/7.87               (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87               (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['123', '191'])).
% 7.66/7.87  thf('193', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ~ (m1_subset_1 @ 
% 7.66/7.87               (sk_D @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0) @ 
% 7.66/7.87               (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (v2_pre_topc @ X0)
% 7.66/7.87          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_pre_topc @ X0))),
% 7.66/7.87      inference('simplify', [status(thm)], ['192'])).
% 7.66/7.87  thf('194', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 7.66/7.87        | ~ (l1_pre_topc @ sk_A)
% 7.66/7.87        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 7.66/7.87        | ~ (v2_pre_topc @ sk_A)
% 7.66/7.87        | ~ (l1_struct_0 @ sk_A)
% 7.66/7.87        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['122', '193'])).
% 7.66/7.87  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('197', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('198', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 7.66/7.87      inference('demod', [status(thm)], ['109', '110'])).
% 7.66/7.87  thf('199', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 7.66/7.87        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))))),
% 7.66/7.87      inference('demod', [status(thm)], ['194', '195', '196', '197', '198'])).
% 7.66/7.87  thf('200', plain,
% 7.66/7.87      (((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('simplify', [status(thm)], ['199'])).
% 7.66/7.87  thf('201', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('202', plain,
% 7.66/7.87      (![X35 : $i, X36 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.66/7.87          | ~ (v2_pre_topc @ X36)
% 7.66/7.87          | ((k2_pre_topc @ X36 @ X35) != (X35))
% 7.66/7.87          | (v4_pre_topc @ X35 @ X36)
% 7.66/7.87          | ~ (l1_pre_topc @ X36))),
% 7.66/7.87      inference('cnf', [status(esa)], [t52_pre_topc])).
% 7.66/7.87  thf('203', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ X0)
% 7.66/7.87          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.87          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0))
% 7.66/7.87          | ~ (v2_pre_topc @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['201', '202'])).
% 7.66/7.87  thf('204', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 7.66/7.87        | ~ (v2_pre_topc @ sk_A)
% 7.66/7.87        | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 7.66/7.87        | ~ (l1_pre_topc @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['200', '203'])).
% 7.66/7.87  thf('205', plain, ((v2_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('207', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 7.66/7.87        | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['204', '205', '206'])).
% 7.66/7.87  thf('208', plain, ((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 7.66/7.87      inference('simplify', [status(thm)], ['207'])).
% 7.66/7.87  thf('209', plain,
% 7.66/7.87      (((v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 7.66/7.87      inference('sup+', [status(thm)], ['33', '208'])).
% 7.66/7.87  thf('210', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('211', plain, ((v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)),
% 7.66/7.87      inference('demod', [status(thm)], ['209', '210'])).
% 7.66/7.87  thf('212', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('213', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf('214', plain,
% 7.66/7.87      (![X35 : $i, X36 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.66/7.87          | ~ (v4_pre_topc @ X35 @ X36)
% 7.66/7.87          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 7.66/7.87          | ~ (l1_pre_topc @ X36))),
% 7.66/7.87      inference('cnf', [status(esa)], [t52_pre_topc])).
% 7.66/7.87  thf('215', plain,
% 7.66/7.87      (![X0 : $i, X1 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 7.66/7.87          | ~ (l1_struct_0 @ X0)
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ((k2_pre_topc @ X0 @ X1) = (X1))
% 7.66/7.87          | ~ (v4_pre_topc @ X1 @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['213', '214'])).
% 7.66/7.87  thf('216', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 7.66/7.87          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 7.66/7.87          | ~ (l1_pre_topc @ X0)
% 7.66/7.87          | ~ (l1_struct_0 @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['212', '215'])).
% 7.66/7.87  thf('217', plain,
% 7.66/7.87      ((~ (l1_struct_0 @ sk_A)
% 7.66/7.87        | ~ (l1_pre_topc @ sk_A)
% 7.66/7.87        | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['211', '216'])).
% 7.66/7.87  thf('218', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('220', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf('221', plain,
% 7.66/7.87      (((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('simplify', [status(thm)], ['199'])).
% 7.66/7.87  thf('222', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)))
% 7.66/7.87        | ~ (l1_struct_0 @ sk_A))),
% 7.66/7.87      inference('sup+', [status(thm)], ['220', '221'])).
% 7.66/7.87  thf('223', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.87      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.87  thf('224', plain,
% 7.66/7.87      (((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)))),
% 7.66/7.87      inference('demod', [status(thm)], ['222', '223'])).
% 7.66/7.87  thf('225', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['217', '218', '219', '224'])).
% 7.66/7.87  thf('226', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 7.66/7.87          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 7.66/7.87             (sk_D @ X0 @ sk_B @ sk_A) @ sk_B @ sk_A)
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 7.66/7.87      inference('demod', [status(thm)], ['32', '225'])).
% 7.66/7.87  thf('227', plain,
% 7.66/7.87      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87        | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.66/7.87        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87        | (zip_tseitin_0 @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.87           (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 7.66/7.87      inference('sup-', [status(thm)], ['20', '226'])).
% 7.66/7.87  thf('228', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('229', plain,
% 7.66/7.87      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87        | (zip_tseitin_0 @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.87           (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A))),
% 7.66/7.87      inference('demod', [status(thm)], ['227', '228'])).
% 7.66/7.87  thf('230', plain,
% 7.66/7.87      (((zip_tseitin_0 @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.87         (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 7.66/7.87        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.87      inference('simplify', [status(thm)], ['229'])).
% 7.66/7.87  thf('231', plain,
% 7.66/7.87      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.66/7.87         ((r1_xboole_0 @ X25 @ X22) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.87  thf('232', plain,
% 7.66/7.87      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87        | (r1_xboole_0 @ sk_B @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['230', '231'])).
% 7.66/7.87  thf('233', plain,
% 7.66/7.87      (![X33 : $i]:
% 7.66/7.87         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.87  thf('234', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.87      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.87  thf('235', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('demod', [status(thm)], ['9', '10'])).
% 7.66/7.87  thf('236', plain,
% 7.66/7.87      (((r2_hidden @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.87         (u1_struct_0 @ sk_A))
% 7.66/7.87        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.87      inference('sup-', [status(thm)], ['234', '235'])).
% 7.66/7.87  thf('237', plain,
% 7.66/7.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('238', plain,
% 7.66/7.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ X29)
% 7.66/7.87          | (m1_subset_1 @ (sk_E @ X29 @ X27 @ X28) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 7.66/7.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.87          | ~ (l1_pre_topc @ X28))),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.87  thf('239', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (l1_pre_topc @ sk_A)
% 7.66/7.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 7.66/7.87      inference('sup-', [status(thm)], ['237', '238'])).
% 7.66/7.87  thf('240', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.87  thf('241', plain,
% 7.66/7.87      (![X0 : $i]:
% 7.66/7.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ((X0) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 7.66/7.87      inference('demod', [status(thm)], ['239', '240'])).
% 7.66/7.87  thf('242', plain,
% 7.66/7.87      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.87        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.87        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.87             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.66/7.87      inference('sup-', [status(thm)], ['236', '241'])).
% 7.66/7.87  thf('243', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.88      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.88  thf('244', plain,
% 7.66/7.88      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88        | (m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.88      inference('demod', [status(thm)], ['242', '243'])).
% 7.66/7.88  thf('245', plain,
% 7.66/7.88      (((m1_subset_1 @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.88      inference('simplify', [status(thm)], ['244'])).
% 7.66/7.88  thf('246', plain,
% 7.66/7.88      ((![X46 : $i]:
% 7.66/7.88          (((X46) = (k1_xboole_0))
% 7.66/7.88           | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88           | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88           | ~ (r1_xboole_0 @ sk_B @ X46)))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('split', [status(esa)], ['0'])).
% 7.66/7.88  thf('247', plain,
% 7.66/7.88      (((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88         | ~ (r1_xboole_0 @ sk_B @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A))
% 7.66/7.88         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 7.66/7.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['245', '246'])).
% 7.66/7.88  thf('248', plain,
% 7.66/7.88      (((~ (r1_xboole_0 @ sk_B @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A))
% 7.66/7.88         | ~ (l1_struct_0 @ sk_A)
% 7.66/7.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 7.66/7.88         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 7.66/7.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['233', '247'])).
% 7.66/7.88  thf('249', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.88      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.88  thf('250', plain,
% 7.66/7.88      (((~ (r1_xboole_0 @ sk_B @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A))
% 7.66/7.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 7.66/7.88         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 7.66/7.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('demod', [status(thm)], ['248', '249'])).
% 7.66/7.88  thf('251', plain,
% 7.66/7.88      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88         | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88         | ~ (v3_pre_topc @ (sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 7.66/7.88         | ((sk_E @ (u1_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['232', '250'])).
% 7.66/7.88  thf('252', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 7.66/7.88      inference('demod', [status(thm)], ['217', '218', '219', '224'])).
% 7.66/7.88  thf('253', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 7.66/7.88      inference('demod', [status(thm)], ['217', '218', '219', '224'])).
% 7.66/7.88  thf('254', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 7.66/7.88      inference('demod', [status(thm)], ['217', '218', '219', '224'])).
% 7.66/7.88  thf('255', plain,
% 7.66/7.88      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88         | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88         | ~ (v3_pre_topc @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 7.66/7.88         | ((sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 7.66/7.88  thf('256', plain,
% 7.66/7.88      (((((sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))
% 7.66/7.88         | ~ (v3_pre_topc @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A)
% 7.66/7.88         | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('simplify', [status(thm)], ['255'])).
% 7.66/7.88  thf('257', plain,
% 7.66/7.88      (((zip_tseitin_0 @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.88         (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 7.66/7.88        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.88      inference('simplify', [status(thm)], ['229'])).
% 7.66/7.88  thf('258', plain,
% 7.66/7.88      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.66/7.88         ((v3_pre_topc @ X22 @ X23) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.88  thf('259', plain,
% 7.66/7.88      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88        | (v3_pre_topc @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_A))),
% 7.66/7.88      inference('sup-', [status(thm)], ['257', '258'])).
% 7.66/7.88  thf('260', plain,
% 7.66/7.88      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88         | ((sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) = (k1_xboole_0))))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('clc', [status(thm)], ['256', '259'])).
% 7.66/7.88  thf('261', plain,
% 7.66/7.88      (((zip_tseitin_0 @ (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.88         (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ sk_B @ sk_A)
% 7.66/7.88        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.66/7.88      inference('simplify', [status(thm)], ['229'])).
% 7.66/7.88  thf('262', plain,
% 7.66/7.88      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.66/7.88         ((r2_hidden @ X24 @ X22) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.88  thf('263', plain,
% 7.66/7.88      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88        | (r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.88           (sk_E @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['261', '262'])).
% 7.66/7.88  thf('264', plain,
% 7.66/7.88      ((((r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ k1_xboole_0)
% 7.66/7.88         | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88         | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('sup+', [status(thm)], ['260', '263'])).
% 7.66/7.88  thf('265', plain,
% 7.66/7.88      (((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88         | (r2_hidden @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_B @ sk_A) @ 
% 7.66/7.88            k1_xboole_0)))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('simplify', [status(thm)], ['264'])).
% 7.66/7.88  thf('266', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 7.66/7.88      inference('clc', [status(thm)], ['97', '106'])).
% 7.66/7.88  thf('267', plain,
% 7.66/7.88      (![X0 : $i]:
% 7.66/7.88         (~ (l1_pre_topc @ X0)
% 7.66/7.88          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 7.66/7.88          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 7.66/7.88      inference('sup-', [status(thm)], ['53', '54'])).
% 7.66/7.88  thf('268', plain,
% 7.66/7.88      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 7.66/7.88        | ~ (l1_pre_topc @ sk_A))),
% 7.66/7.88      inference('sup-', [status(thm)], ['266', '267'])).
% 7.66/7.88  thf('269', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('270', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 7.66/7.88      inference('demod', [status(thm)], ['268', '269'])).
% 7.66/7.88  thf('271', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.88      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.88  thf('272', plain,
% 7.66/7.88      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.88      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.88  thf('273', plain,
% 7.66/7.88      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 7.66/7.88         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.66/7.88          | ~ (r2_hidden @ X39 @ (k2_pre_topc @ X38 @ X37))
% 7.66/7.88          | ~ (r1_xboole_0 @ X37 @ X40)
% 7.66/7.88          | ~ (r2_hidden @ X39 @ X40)
% 7.66/7.88          | ~ (v3_pre_topc @ X40 @ X38)
% 7.66/7.88          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.66/7.88          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 7.66/7.88          | ~ (l1_pre_topc @ X38))),
% 7.66/7.88      inference('cnf', [status(esa)], [t54_pre_topc])).
% 7.66/7.88  thf('274', plain,
% 7.66/7.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.88         (~ (l1_pre_topc @ X0)
% 7.66/7.88          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.88          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.88          | ~ (v3_pre_topc @ X2 @ X0)
% 7.66/7.88          | ~ (r2_hidden @ X1 @ X2)
% 7.66/7.88          | ~ (r1_xboole_0 @ k1_xboole_0 @ X2)
% 7.66/7.88          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['272', '273'])).
% 7.66/7.88  thf('275', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 7.66/7.88      inference('simplify', [status(thm)], ['77'])).
% 7.66/7.88  thf('276', plain,
% 7.66/7.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.88         (~ (l1_pre_topc @ X0)
% 7.66/7.88          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.88          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.88          | ~ (v3_pre_topc @ X2 @ X0)
% 7.66/7.88          | ~ (r2_hidden @ X1 @ X2)
% 7.66/7.88          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 7.66/7.88      inference('demod', [status(thm)], ['274', '275'])).
% 7.66/7.88  thf('277', plain,
% 7.66/7.88      (![X0 : $i, X1 : $i]:
% 7.66/7.88         (~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ k1_xboole_0))
% 7.66/7.88          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.88          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 7.66/7.88          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 7.66/7.88          | ~ (l1_pre_topc @ X0))),
% 7.66/7.88      inference('sup-', [status(thm)], ['271', '276'])).
% 7.66/7.88  thf('278', plain,
% 7.66/7.88      (![X0 : $i]:
% 7.66/7.88         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 7.66/7.88          | ~ (l1_pre_topc @ sk_A)
% 7.66/7.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.66/7.88          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 7.66/7.88          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['270', '277'])).
% 7.66/7.88  thf('279', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('280', plain,
% 7.66/7.88      (![X0 : $i]:
% 7.66/7.88         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 7.66/7.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.66/7.88          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 7.66/7.88          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.88      inference('demod', [status(thm)], ['278', '279'])).
% 7.66/7.88  thf('281', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 7.66/7.88      inference('demod', [status(thm)], ['109', '110'])).
% 7.66/7.88  thf('282', plain,
% 7.66/7.88      (![X0 : $i]:
% 7.66/7.88         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 7.66/7.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.66/7.88          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.88      inference('demod', [status(thm)], ['280', '281'])).
% 7.66/7.88  thf('283', plain,
% 7.66/7.88      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.88      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.88  thf('284', plain,
% 7.66/7.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.66/7.88         (~ (r2_hidden @ X19 @ X20)
% 7.66/7.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 7.66/7.88          | (m1_subset_1 @ X19 @ X21))),
% 7.66/7.88      inference('cnf', [status(esa)], [t4_subset])).
% 7.66/7.88  thf('285', plain,
% 7.66/7.88      (![X0 : $i, X1 : $i]:
% 7.66/7.88         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 7.66/7.88      inference('sup-', [status(thm)], ['283', '284'])).
% 7.66/7.88  thf('286', plain,
% 7.66/7.88      (![X0 : $i]:
% 7.66/7.88         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 7.66/7.88          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 7.66/7.88      inference('clc', [status(thm)], ['282', '285'])).
% 7.66/7.88  thf('287', plain,
% 7.66/7.88      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.88      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.88  thf(l3_subset_1, axiom,
% 7.66/7.88    (![A:$i,B:$i]:
% 7.66/7.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.66/7.88       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 7.66/7.88  thf('288', plain,
% 7.66/7.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.66/7.88         (~ (r2_hidden @ X13 @ X14)
% 7.66/7.88          | (r2_hidden @ X13 @ X15)
% 7.66/7.88          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 7.66/7.88      inference('cnf', [status(esa)], [l3_subset_1])).
% 7.66/7.88  thf('289', plain,
% 7.66/7.88      (![X0 : $i, X1 : $i]:
% 7.66/7.88         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 7.66/7.88      inference('sup-', [status(thm)], ['287', '288'])).
% 7.66/7.88  thf('290', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 7.66/7.88      inference('clc', [status(thm)], ['286', '289'])).
% 7.66/7.88  thf('291', plain,
% 7.66/7.88      ((((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('clc', [status(thm)], ['265', '290'])).
% 7.66/7.88  thf('292', plain,
% 7.66/7.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf(d3_tops_1, axiom,
% 7.66/7.88    (![A:$i]:
% 7.66/7.88     ( ( l1_pre_topc @ A ) =>
% 7.66/7.88       ( ![B:$i]:
% 7.66/7.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.66/7.88           ( ( v1_tops_1 @ B @ A ) <=>
% 7.66/7.88             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 7.66/7.88  thf('293', plain,
% 7.66/7.88      (![X41 : $i, X42 : $i]:
% 7.66/7.88         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 7.66/7.88          | ((k2_pre_topc @ X42 @ X41) != (k2_struct_0 @ X42))
% 7.66/7.88          | (v1_tops_1 @ X41 @ X42)
% 7.66/7.88          | ~ (l1_pre_topc @ X42))),
% 7.66/7.88      inference('cnf', [status(esa)], [d3_tops_1])).
% 7.66/7.88  thf('294', plain,
% 7.66/7.88      ((~ (l1_pre_topc @ sk_A)
% 7.66/7.88        | (v1_tops_1 @ sk_B @ sk_A)
% 7.66/7.88        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['292', '293'])).
% 7.66/7.88  thf('295', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('296', plain,
% 7.66/7.88      (((v1_tops_1 @ sk_B @ sk_A)
% 7.66/7.88        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 7.66/7.88      inference('demod', [status(thm)], ['294', '295'])).
% 7.66/7.88  thf('297', plain,
% 7.66/7.88      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 7.66/7.88         | (v1_tops_1 @ sk_B @ sk_A)))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['291', '296'])).
% 7.66/7.88  thf('298', plain,
% 7.66/7.88      (((v1_tops_1 @ sk_B @ sk_A))
% 7.66/7.88         <= ((![X46 : $i]:
% 7.66/7.88                (((X46) = (k1_xboole_0))
% 7.66/7.88                 | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88                 | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88                 | ~ (r1_xboole_0 @ sk_B @ X46))))),
% 7.66/7.88      inference('simplify', [status(thm)], ['297'])).
% 7.66/7.88  thf('299', plain,
% 7.66/7.88      (((r1_xboole_0 @ sk_B @ sk_C) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('300', plain,
% 7.66/7.88      ((~ (v1_tops_1 @ sk_B @ sk_A)) <= (~ ((v1_tops_1 @ sk_B @ sk_A)))),
% 7.66/7.88      inference('split', [status(esa)], ['299'])).
% 7.66/7.88  thf('301', plain,
% 7.66/7.88      (~
% 7.66/7.88       (![X46 : $i]:
% 7.66/7.88          (((X46) = (k1_xboole_0))
% 7.66/7.88           | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88           | ~ (v3_pre_topc @ X46 @ sk_A)
% 7.66/7.88           | ~ (r1_xboole_0 @ sk_B @ X46))) | 
% 7.66/7.88       ((v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('sup-', [status(thm)], ['298', '300'])).
% 7.66/7.88  thf('302', plain,
% 7.66/7.88      (((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('split', [status(esa)], ['299'])).
% 7.66/7.88  thf('303', plain,
% 7.66/7.88      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('304', plain,
% 7.66/7.88      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('split', [status(esa)], ['303'])).
% 7.66/7.88  thf('305', plain,
% 7.66/7.88      ((((sk_C) != (k1_xboole_0)) | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('306', plain,
% 7.66/7.88      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('split', [status(esa)], ['305'])).
% 7.66/7.88  thf('307', plain,
% 7.66/7.88      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('308', plain,
% 7.66/7.88      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 7.66/7.88       ~ ((v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('split', [status(esa)], ['307'])).
% 7.66/7.88  thf('309', plain,
% 7.66/7.88      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('split', [status(esa)], ['307'])).
% 7.66/7.88  thf('310', plain,
% 7.66/7.88      (![X0 : $i, X1 : $i]:
% 7.66/7.88         (~ (l1_pre_topc @ X0)
% 7.66/7.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.88          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 7.66/7.88          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['59', '60'])).
% 7.66/7.88  thf('311', plain,
% 7.66/7.88      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.66/7.88         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.88         | ~ (l1_pre_topc @ sk_A)))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['309', '310'])).
% 7.66/7.88  thf('312', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('313', plain,
% 7.66/7.88      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 7.66/7.88         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('demod', [status(thm)], ['311', '312'])).
% 7.66/7.88  thf('314', plain,
% 7.66/7.88      (![X0 : $i]:
% 7.66/7.88         ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0 @ sk_A)
% 7.66/7.88          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['111', '112'])).
% 7.66/7.88  thf('315', plain,
% 7.66/7.88      (((((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.88         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.88            (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['313', '314'])).
% 7.66/7.88  thf('316', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 7.66/7.88      inference('demod', [status(thm)], ['268', '269'])).
% 7.66/7.88  thf('317', plain,
% 7.66/7.88      (((((sk_C) = (k1_xboole_0))
% 7.66/7.88         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.88            (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('demod', [status(thm)], ['315', '316'])).
% 7.66/7.88  thf('318', plain,
% 7.66/7.88      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 7.66/7.88      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.66/7.88  thf('319', plain,
% 7.66/7.88      (![X27 : $i, X28 : $i, X29 : $i, X32 : $i]:
% 7.66/7.88         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.88          | (r2_hidden @ (sk_D @ X29 @ X27 @ X28) @ X29)
% 7.66/7.88          | ~ (zip_tseitin_0 @ X32 @ (sk_D @ X29 @ X27 @ X28) @ X27 @ X28)
% 7.66/7.88          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.88          | ((X29) = (k2_pre_topc @ X28 @ X27))
% 7.66/7.88          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.88          | ~ (l1_pre_topc @ X28))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.88  thf('320', plain,
% 7.66/7.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.66/7.88         (~ (l1_pre_topc @ X0)
% 7.66/7.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.88          | ((X1) = (k2_pre_topc @ X0 @ k1_xboole_0))
% 7.66/7.88          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.88          | ~ (zip_tseitin_0 @ X2 @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 7.66/7.88               k1_xboole_0 @ X0)
% 7.66/7.88          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 7.66/7.88      inference('sup-', [status(thm)], ['318', '319'])).
% 7.66/7.88  thf('321', plain,
% 7.66/7.88      (((((sk_C) = (k1_xboole_0))
% 7.66/7.88         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 7.66/7.88         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.88              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88         | ((sk_C) = (k2_pre_topc @ sk_A @ k1_xboole_0))
% 7.66/7.88         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88         | ~ (l1_pre_topc @ sk_A)))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['317', '320'])).
% 7.66/7.88  thf('322', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.88      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.88  thf('323', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 7.66/7.88      inference('demod', [status(thm)], ['268', '269'])).
% 7.66/7.88  thf('324', plain,
% 7.66/7.88      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('split', [status(esa)], ['307'])).
% 7.66/7.88  thf('325', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('326', plain,
% 7.66/7.88      (((((sk_C) = (k1_xboole_0))
% 7.66/7.88         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 7.66/7.88         | ((sk_C) = (k1_xboole_0))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('demod', [status(thm)], ['321', '322', '323', '324', '325'])).
% 7.66/7.88  thf('327', plain,
% 7.66/7.88      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 7.66/7.88         | ((sk_C) = (k1_xboole_0))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('simplify', [status(thm)], ['326'])).
% 7.66/7.88  thf('328', plain,
% 7.66/7.88      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 7.66/7.88      inference('split', [status(esa)], ['303'])).
% 7.66/7.88  thf('329', plain,
% 7.66/7.88      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 7.66/7.88      inference('split', [status(esa)], ['299'])).
% 7.66/7.88  thf('330', plain,
% 7.66/7.88      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 7.66/7.88         ((zip_tseitin_0 @ X22 @ X24 @ X25 @ X26)
% 7.66/7.88          | ~ (r1_xboole_0 @ X25 @ X22)
% 7.66/7.88          | ~ (r2_hidden @ X24 @ X22)
% 7.66/7.88          | ~ (v3_pre_topc @ X22 @ X26))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.88  thf('331', plain,
% 7.66/7.88      ((![X0 : $i, X1 : $i]:
% 7.66/7.88          (~ (v3_pre_topc @ sk_C @ X0)
% 7.66/7.88           | ~ (r2_hidden @ X1 @ sk_C)
% 7.66/7.88           | (zip_tseitin_0 @ sk_C @ X1 @ sk_B @ X0)))
% 7.66/7.88         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['329', '330'])).
% 7.66/7.88  thf('332', plain,
% 7.66/7.88      ((![X0 : $i]:
% 7.66/7.88          ((zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A)
% 7.66/7.88           | ~ (r2_hidden @ X0 @ sk_C)))
% 7.66/7.88         <= (((r1_xboole_0 @ sk_B @ sk_C)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['328', '331'])).
% 7.66/7.88  thf('333', plain,
% 7.66/7.88      (((((sk_C) = (k1_xboole_0))
% 7.66/7.88         | (zip_tseitin_0 @ sk_C @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_B @ 
% 7.66/7.88            sk_A)))
% 7.66/7.88         <= (((r1_xboole_0 @ sk_B @ sk_C)) & 
% 7.66/7.88             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 7.66/7.88             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['327', '332'])).
% 7.66/7.88  thf('334', plain,
% 7.66/7.88      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('split', [status(esa)], ['307'])).
% 7.66/7.88  thf('335', plain,
% 7.66/7.88      (((v1_tops_1 @ sk_B @ sk_A)) <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 7.66/7.88      inference('split', [status(esa)], ['0'])).
% 7.66/7.88  thf('336', plain,
% 7.66/7.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('337', plain,
% 7.66/7.88      (![X41 : $i, X42 : $i]:
% 7.66/7.88         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 7.66/7.88          | ~ (v1_tops_1 @ X41 @ X42)
% 7.66/7.88          | ((k2_pre_topc @ X42 @ X41) = (k2_struct_0 @ X42))
% 7.66/7.88          | ~ (l1_pre_topc @ X42))),
% 7.66/7.88      inference('cnf', [status(esa)], [d3_tops_1])).
% 7.66/7.88  thf('338', plain,
% 7.66/7.88      ((~ (l1_pre_topc @ sk_A)
% 7.66/7.88        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 7.66/7.88        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('sup-', [status(thm)], ['336', '337'])).
% 7.66/7.88  thf('339', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('340', plain,
% 7.66/7.88      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 7.66/7.88        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 7.66/7.88      inference('demod', [status(thm)], ['338', '339'])).
% 7.66/7.88  thf('341', plain,
% 7.66/7.88      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 7.66/7.88         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['335', '340'])).
% 7.66/7.88  thf('342', plain,
% 7.66/7.88      (![X33 : $i]:
% 7.66/7.88         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.88  thf('343', plain,
% 7.66/7.88      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 7.66/7.88         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.88          | ((X29) != (k2_pre_topc @ X28 @ X27))
% 7.66/7.88          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.88          | ~ (zip_tseitin_0 @ X30 @ X31 @ X27 @ X28)
% 7.66/7.88          | ~ (r2_hidden @ X31 @ X29)
% 7.66/7.88          | ~ (r2_hidden @ X31 @ (u1_struct_0 @ X28))
% 7.66/7.88          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.88          | ~ (l1_pre_topc @ X28))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.66/7.88  thf('344', plain,
% 7.66/7.88      (![X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 7.66/7.88         (~ (l1_pre_topc @ X28)
% 7.66/7.88          | ~ (m1_subset_1 @ (k2_pre_topc @ X28 @ X27) @ 
% 7.66/7.88               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.88          | ~ (r2_hidden @ X31 @ (u1_struct_0 @ X28))
% 7.66/7.88          | ~ (r2_hidden @ X31 @ (k2_pre_topc @ X28 @ X27))
% 7.66/7.88          | ~ (zip_tseitin_0 @ X30 @ X31 @ X27 @ X28)
% 7.66/7.88          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.66/7.88          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 7.66/7.88      inference('simplify', [status(thm)], ['343'])).
% 7.66/7.88  thf('345', plain,
% 7.66/7.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.66/7.88         (~ (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 7.66/7.88             (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 7.66/7.88          | ~ (l1_struct_0 @ X0)
% 7.66/7.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.88          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.66/7.88          | ~ (zip_tseitin_0 @ X2 @ X3 @ X1 @ X0)
% 7.66/7.88          | ~ (r2_hidden @ X3 @ (k2_pre_topc @ X0 @ X1))
% 7.66/7.88          | ~ (r2_hidden @ X3 @ (u1_struct_0 @ X0))
% 7.66/7.88          | ~ (l1_pre_topc @ X0))),
% 7.66/7.88      inference('sup-', [status(thm)], ['342', '344'])).
% 7.66/7.88  thf('346', plain,
% 7.66/7.88      ((![X0 : $i, X1 : $i]:
% 7.66/7.88          (~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.66/7.88              (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.66/7.88           | ~ (l1_pre_topc @ sk_A)
% 7.66/7.88           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 7.66/7.88           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 7.66/7.88           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 7.66/7.88           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.66/7.88           | ~ (l1_struct_0 @ sk_A)))
% 7.66/7.88         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['341', '345'])).
% 7.66/7.88  thf('347', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 7.66/7.88      inference('demod', [status(thm)], ['3', '4'])).
% 7.66/7.88  thf('348', plain, ((l1_pre_topc @ sk_A)),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('349', plain,
% 7.66/7.88      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))
% 7.66/7.88         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 7.66/7.88      inference('sup-', [status(thm)], ['335', '340'])).
% 7.66/7.88  thf('350', plain,
% 7.66/7.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.66/7.88  thf('351', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.88      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.88  thf('352', plain,
% 7.66/7.88      ((![X0 : $i, X1 : $i]:
% 7.66/7.88          (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 7.66/7.88           | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 7.66/7.88           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 7.66/7.88           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 7.66/7.88         <= (((v1_tops_1 @ sk_B @ sk_A)))),
% 7.66/7.88      inference('demod', [status(thm)],
% 7.66/7.88                ['346', '347', '348', '349', '350', '351'])).
% 7.66/7.88  thf('353', plain,
% 7.66/7.88      ((![X0 : $i]:
% 7.66/7.88          (~ (zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A)
% 7.66/7.88           | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 7.66/7.88           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))))
% 7.66/7.88         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 7.66/7.88             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['334', '352'])).
% 7.66/7.88  thf('354', plain,
% 7.66/7.88      (((((sk_C) = (k1_xboole_0))
% 7.66/7.88         | ~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 7.66/7.88              (u1_struct_0 @ sk_A))
% 7.66/7.88         | ~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 7.66/7.88              (k2_struct_0 @ sk_A))))
% 7.66/7.88         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 7.66/7.88             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 7.66/7.88             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 7.66/7.88             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['333', '353'])).
% 7.66/7.88  thf('355', plain,
% 7.66/7.88      (((((sk_C) = (k1_xboole_0))
% 7.66/7.88         | (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.66/7.88            (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0 @ sk_A)))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('demod', [status(thm)], ['315', '316'])).
% 7.66/7.88  thf('356', plain,
% 7.66/7.88      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 7.66/7.88         ((r2_hidden @ X24 @ X22) | ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X23))),
% 7.66/7.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.66/7.88  thf('357', plain,
% 7.66/7.88      (((((sk_C) = (k1_xboole_0))
% 7.66/7.88         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 7.66/7.88            (u1_struct_0 @ sk_A))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['355', '356'])).
% 7.66/7.88  thf('358', plain,
% 7.66/7.88      (((~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 7.66/7.88            (k2_struct_0 @ sk_A))
% 7.66/7.88         | ((sk_C) = (k1_xboole_0))))
% 7.66/7.88         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 7.66/7.88             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 7.66/7.88             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 7.66/7.88             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('clc', [status(thm)], ['354', '357'])).
% 7.66/7.88  thf('359', plain,
% 7.66/7.88      ((((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ sk_C)
% 7.66/7.88         | ((sk_C) = (k1_xboole_0))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('simplify', [status(thm)], ['326'])).
% 7.66/7.88  thf('360', plain,
% 7.66/7.88      (![X33 : $i]:
% 7.66/7.88         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 7.66/7.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.66/7.88  thf('361', plain,
% 7.66/7.88      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('split', [status(esa)], ['307'])).
% 7.66/7.88  thf('362', plain,
% 7.66/7.88      ((((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.66/7.88         | ~ (l1_struct_0 @ sk_A)))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup+', [status(thm)], ['360', '361'])).
% 7.66/7.88  thf('363', plain, ((l1_struct_0 @ sk_A)),
% 7.66/7.88      inference('sup-', [status(thm)], ['13', '14'])).
% 7.66/7.88  thf('364', plain,
% 7.66/7.88      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('demod', [status(thm)], ['362', '363'])).
% 7.66/7.88  thf('365', plain,
% 7.66/7.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.66/7.88         (~ (r2_hidden @ X13 @ X14)
% 7.66/7.88          | (r2_hidden @ X13 @ X15)
% 7.66/7.88          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 7.66/7.88      inference('cnf', [status(esa)], [l3_subset_1])).
% 7.66/7.88  thf('366', plain,
% 7.66/7.88      ((![X0 : $i]:
% 7.66/7.88          ((r2_hidden @ X0 @ (k2_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C)))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['364', '365'])).
% 7.66/7.88  thf('367', plain,
% 7.66/7.88      (((((sk_C) = (k1_xboole_0))
% 7.66/7.88         | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ sk_A) @ 
% 7.66/7.88            (k2_struct_0 @ sk_A))))
% 7.66/7.88         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['359', '366'])).
% 7.66/7.88  thf('368', plain,
% 7.66/7.88      ((((sk_C) = (k1_xboole_0)))
% 7.66/7.88         <= (((v1_tops_1 @ sk_B @ sk_A)) & 
% 7.66/7.88             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 7.66/7.88             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 7.66/7.88             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('clc', [status(thm)], ['358', '367'])).
% 7.66/7.88  thf('369', plain,
% 7.66/7.88      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 7.66/7.88      inference('split', [status(esa)], ['305'])).
% 7.66/7.88  thf('370', plain,
% 7.66/7.88      ((((sk_C) != (sk_C)))
% 7.66/7.88         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 7.66/7.88             ((v1_tops_1 @ sk_B @ sk_A)) & 
% 7.66/7.88             ((r1_xboole_0 @ sk_B @ sk_C)) & 
% 7.66/7.88             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 7.66/7.88             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.66/7.88      inference('sup-', [status(thm)], ['368', '369'])).
% 7.66/7.88  thf('371', plain,
% 7.66/7.88      (~ ((v1_tops_1 @ sk_B @ sk_A)) | 
% 7.66/7.88       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 7.66/7.88       ~ ((r1_xboole_0 @ sk_B @ sk_C)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 7.66/7.88       (((sk_C) = (k1_xboole_0)))),
% 7.66/7.88      inference('simplify', [status(thm)], ['370'])).
% 7.66/7.88  thf('372', plain, ($false),
% 7.66/7.88      inference('sat_resolution*', [status(thm)],
% 7.66/7.88                ['1', '301', '302', '304', '306', '308', '371'])).
% 7.66/7.88  
% 7.66/7.88  % SZS output end Refutation
% 7.66/7.88  
% 7.66/7.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
