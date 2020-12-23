%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1NycZmtgC6

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:18 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 193 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          : 1270 (2997 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('0',plain,(
    ! [X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X21 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( r1_tarski @ X21 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k1_tops_1 @ X13 @ X12 ) )
      | ( v3_pre_topc @ ( sk_D @ X12 @ X14 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( v3_pre_topc @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k1_tops_1 @ X13 @ X12 ) )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X14 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,
    ( ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_B )
        | ~ ( v3_pre_topc @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A )
        | ( ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
          = k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
          = k1_xboole_0 )
        | ~ ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_B )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_B )
        | ( ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
          = k1_xboole_0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k1_tops_1 @ X13 @ X12 ) )
      | ( r1_tarski @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
          = k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k1_tops_1 @ X13 @ X12 ) )
      | ( r2_hidden @ X14 @ ( sk_D @ X12 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ X19 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ~ ! [X21: $i] :
          ( ( X21 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X21 @ sk_A )
          | ~ ( r1_tarski @ X21 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tops_1 @ X19 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X19 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['60'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['72','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('86',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('88',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','61','63','65','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1NycZmtgC6
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 286 iterations in 0.116s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.56  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(t86_tops_1, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( v2_tops_1 @ B @ A ) <=>
% 0.37/0.56             ( ![C:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.37/0.56                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56              ( ( v2_tops_1 @ B @ A ) <=>
% 0.37/0.56                ( ![C:$i]:
% 0.37/0.56                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.37/0.56                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (![X21 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | ((X21) = (k1_xboole_0))
% 0.37/0.56          | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56          | ~ (r1_tarski @ X21 @ sk_B)
% 0.37/0.56          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((![X21 : $i]:
% 0.37/0.56          (((X21) = (k1_xboole_0))
% 0.37/0.56           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56           | ~ (r1_tarski @ X21 @ sk_B))) | 
% 0.37/0.56       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf(d3_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t54_tops_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i,C:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.37/0.56             ( ?[D:$i]:
% 0.37/0.56               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.37/0.56                 ( v3_pre_topc @ D @ A ) & 
% 0.37/0.56                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.56          | ~ (r2_hidden @ X14 @ (k1_tops_1 @ X13 @ X12))
% 0.37/0.56          | (v3_pre_topc @ (sk_D @ X12 @ X14 @ X13) @ X13)
% 0.37/0.56          | ~ (l1_pre_topc @ X13)
% 0.37/0.56          | ~ (v2_pre_topc @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | (v3_pre_topc @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v3_pre_topc @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56          | (v3_pre_topc @ 
% 0.37/0.56             (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.37/0.56             sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '8'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.56          | ~ (r2_hidden @ X14 @ (k1_tops_1 @ X13 @ X12))
% 0.37/0.56          | (m1_subset_1 @ (sk_D @ X12 @ X14 @ X13) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.56          | ~ (l1_pre_topc @ X13)
% 0.37/0.56          | ~ (v2_pre_topc @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56          | (m1_subset_1 @ 
% 0.37/0.56             (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      ((![X21 : $i]:
% 0.37/0.56          (((X21) = (k1_xboole_0))
% 0.37/0.56           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56           | ~ (r1_tarski @ X21 @ sk_B)))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56           | ~ (r1_tarski @ 
% 0.37/0.56                (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.37/0.56                sk_B)
% 0.37/0.56           | ~ (v3_pre_topc @ 
% 0.37/0.56                (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.37/0.56                sk_A)
% 0.37/0.56           | ((sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.37/0.56               = (k1_xboole_0))))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56           | ((sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.37/0.56               = (k1_xboole_0))
% 0.37/0.56           | ~ (r1_tarski @ 
% 0.37/0.56                (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.37/0.56                sk_B)
% 0.37/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (~ (r1_tarski @ 
% 0.37/0.56              (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.37/0.56              sk_B)
% 0.37/0.56           | ((sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.37/0.56               = (k1_xboole_0))
% 0.37/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.56          | ~ (r2_hidden @ X14 @ (k1_tops_1 @ X13 @ X12))
% 0.37/0.56          | (r1_tarski @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.37/0.56          | ~ (l1_pre_topc @ X13)
% 0.37/0.56          | ~ (v2_pre_topc @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | (r1_tarski @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56          | (r1_tarski @ 
% 0.37/0.56             (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.37/0.56             sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '28'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56           | ((sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.37/0.56               = (k1_xboole_0))))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('clc', [status(thm)], ['21', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.56          | ~ (r2_hidden @ X14 @ (k1_tops_1 @ X13 @ X12))
% 0.37/0.56          | (r2_hidden @ X14 @ (sk_D @ X12 @ X14 @ X13))
% 0.37/0.56          | ~ (l1_pre_topc @ X13)
% 0.37/0.56          | ~ (v2_pre_topc @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | (r2_hidden @ X0 @ (sk_D @ sk_B @ X0 @ sk_A))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r2_hidden @ X0 @ (sk_D @ sk_B @ X0 @ sk_A))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.37/0.56             (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['31', '37'])).
% 0.37/0.56  thf(t7_ordinal1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56          | ~ (r1_tarski @ 
% 0.37/0.56               (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.37/0.56               (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['30', '40'])).
% 0.37/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.56  thf('42', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.37/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      ((![X0 : $i]: (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.56  thf('45', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.56  thf(d10_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X4 : $i, X6 : $i]:
% 0.37/0.56         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['44', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t84_tops_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( v2_tops_1 @ B @ A ) <=>
% 0.37/0.56             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.56          | ((k1_tops_1 @ X20 @ X19) != (k1_xboole_0))
% 0.37/0.56          | (v2_tops_1 @ X19 @ X20)
% 0.37/0.56          | ~ (l1_pre_topc @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v2_tops_1 @ sk_B @ sk_A)
% 0.37/0.56        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (((v2_tops_1 @ sk_B @ sk_A)
% 0.37/0.56        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['48', '53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (((v2_tops_1 @ sk_B @ sk_A))
% 0.37/0.56         <= ((![X21 : $i]:
% 0.37/0.56                (((X21) = (k1_xboole_0))
% 0.37/0.56                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['56'])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (~
% 0.37/0.56       (![X21 : $i]:
% 0.37/0.56          (((X21) = (k1_xboole_0))
% 0.37/0.56           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.37/0.56           | ~ (r1_tarski @ X21 @ sk_B))) | 
% 0.37/0.56       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['55', '57'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('split', [status(esa)], ['56'])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('split', [status(esa)], ['60'])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('split', [status(esa)], ['62'])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.37/0.57       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('split', [status(esa)], ['64'])).
% 0.37/0.57  thf('66', plain,
% 0.37/0.57      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.57          | ~ (v2_tops_1 @ X19 @ X20)
% 0.37/0.57          | ((k1_tops_1 @ X20 @ X19) = (k1_xboole_0))
% 0.37/0.57          | ~ (l1_pre_topc @ X20))),
% 0.37/0.57      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.37/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.57  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('71', plain,
% 0.37/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.37/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['69', '70'])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.37/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['66', '71'])).
% 0.37/0.57  thf('73', plain,
% 0.37/0.57      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['56'])).
% 0.37/0.57  thf('74', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('75', plain,
% 0.37/0.57      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['60'])).
% 0.37/0.57  thf('76', plain,
% 0.37/0.57      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.57         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('split', [status(esa)], ['64'])).
% 0.37/0.57  thf(t56_tops_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.57                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('77', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (v3_pre_topc @ X16 @ X17)
% 0.37/0.57          | ~ (r1_tarski @ X16 @ X18)
% 0.37/0.57          | (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (l1_pre_topc @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.37/0.57  thf('78', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          (~ (l1_pre_topc @ sk_A)
% 0.37/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.37/0.57           | ~ (r1_tarski @ sk_C_1 @ X0)
% 0.37/0.57           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 0.37/0.57         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.57  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('80', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.37/0.57           | ~ (r1_tarski @ sk_C_1 @ X0)
% 0.37/0.57           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 0.37/0.57         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('demod', [status(thm)], ['78', '79'])).
% 0.37/0.57  thf('81', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          (~ (r1_tarski @ sk_C_1 @ X0)
% 0.37/0.57           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.37/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.57         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.37/0.57             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['75', '80'])).
% 0.37/0.57  thf('82', plain,
% 0.37/0.57      ((((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.57         | ~ (r1_tarski @ sk_C_1 @ sk_B)))
% 0.37/0.57         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.37/0.57             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['74', '81'])).
% 0.37/0.57  thf('83', plain,
% 0.37/0.57      (((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.37/0.57             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.37/0.57             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['73', '82'])).
% 0.37/0.57  thf('84', plain,
% 0.37/0.57      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 0.37/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.37/0.57             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.37/0.57             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.37/0.57             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['72', '83'])).
% 0.37/0.57  thf('85', plain,
% 0.37/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('86', plain,
% 0.37/0.57      ((((sk_C_1) = (k1_xboole_0)))
% 0.37/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.37/0.57             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.37/0.57             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.37/0.57             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['84', '85'])).
% 0.37/0.57  thf('87', plain,
% 0.37/0.57      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.37/0.57      inference('split', [status(esa)], ['62'])).
% 0.37/0.57  thf('88', plain,
% 0.37/0.57      ((((sk_C_1) != (sk_C_1)))
% 0.37/0.57         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 0.37/0.57             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.37/0.57             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.37/0.57             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.37/0.57             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.37/0.57  thf('89', plain,
% 0.37/0.57      (~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.37/0.57       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.37/0.57       ~ ((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | 
% 0.37/0.57       (((sk_C_1) = (k1_xboole_0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['88'])).
% 0.37/0.57  thf('90', plain, ($false),
% 0.37/0.57      inference('sat_resolution*', [status(thm)],
% 0.37/0.57                ['1', '58', '59', '61', '63', '65', '89'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
