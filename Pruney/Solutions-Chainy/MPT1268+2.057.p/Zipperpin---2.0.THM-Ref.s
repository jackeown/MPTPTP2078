%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xnQZqy9xBe

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:24 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 174 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  884 (2395 expanded)
%              Number of equality atoms :   36 (  92 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf('0',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( r1_tarski @ X23 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B_1 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('24',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','21','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ~ ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('40',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('47',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('48',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('50',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_B_1 @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('57',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X17 )
      | ~ ( v3_pre_topc @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r2_hidden @ X19 @ ( k1_tops_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( r1_tarski @ sk_C @ sk_B_1 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( v3_pre_topc @ sk_C @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','65'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('68',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ sk_C ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','68'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('70',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','38','39','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xnQZqy9xBe
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.78  % Solved by: fo/fo7.sh
% 0.57/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.78  % done 843 iterations in 0.334s
% 0.57/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.78  % SZS output start Refutation
% 0.57/0.78  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.57/0.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.57/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.57/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.78  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.57/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.78  thf(sk_B_type, type, sk_B: $i > $i).
% 0.57/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.78  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.57/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.78  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.57/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.57/0.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.57/0.78  thf(t86_tops_1, conjecture,
% 0.57/0.78    (![A:$i]:
% 0.57/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.78       ( ![B:$i]:
% 0.57/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.78           ( ( v2_tops_1 @ B @ A ) <=>
% 0.57/0.78             ( ![C:$i]:
% 0.57/0.78               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.78                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.57/0.78                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.57/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.78    (~( ![A:$i]:
% 0.57/0.78        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.78          ( ![B:$i]:
% 0.57/0.78            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.78              ( ( v2_tops_1 @ B @ A ) <=>
% 0.57/0.78                ( ![C:$i]:
% 0.57/0.78                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.78                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.57/0.78                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.57/0.78    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.57/0.78  thf('0', plain,
% 0.57/0.78      ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('1', plain,
% 0.57/0.78      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('split', [status(esa)], ['0'])).
% 0.57/0.78  thf('2', plain,
% 0.57/0.78      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('3', plain,
% 0.57/0.78      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('split', [status(esa)], ['2'])).
% 0.57/0.78  thf('4', plain,
% 0.57/0.78      (![X23 : $i]:
% 0.57/0.78         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78          | ((X23) = (k1_xboole_0))
% 0.57/0.78          | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78          | ~ (r1_tarski @ X23 @ sk_B_1)
% 0.57/0.78          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('5', plain,
% 0.57/0.78      ((![X23 : $i]:
% 0.57/0.78          (((X23) = (k1_xboole_0))
% 0.57/0.78           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78           | ~ (r1_tarski @ X23 @ sk_B_1))) | 
% 0.57/0.78       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('split', [status(esa)], ['4'])).
% 0.57/0.78  thf('6', plain,
% 0.57/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf(t3_subset, axiom,
% 0.57/0.78    (![A:$i,B:$i]:
% 0.57/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.78  thf('7', plain,
% 0.57/0.78      (![X4 : $i, X5 : $i]:
% 0.57/0.78         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.57/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.78  thf('8', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.57/0.78      inference('sup-', [status(thm)], ['6', '7'])).
% 0.57/0.78  thf('9', plain,
% 0.57/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf(t44_tops_1, axiom,
% 0.57/0.78    (![A:$i]:
% 0.57/0.78     ( ( l1_pre_topc @ A ) =>
% 0.57/0.78       ( ![B:$i]:
% 0.57/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.78           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.57/0.78  thf('10', plain,
% 0.57/0.78      (![X15 : $i, X16 : $i]:
% 0.57/0.78         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.57/0.78          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ X15)
% 0.57/0.78          | ~ (l1_pre_topc @ X16))),
% 0.57/0.78      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.57/0.78  thf('11', plain,
% 0.57/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.57/0.78        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.57/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.57/0.78  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.57/0.78      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.78  thf(t1_xboole_1, axiom,
% 0.57/0.78    (![A:$i,B:$i,C:$i]:
% 0.57/0.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.57/0.78       ( r1_tarski @ A @ C ) ))).
% 0.57/0.78  thf('14', plain,
% 0.57/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.78         (~ (r1_tarski @ X0 @ X1)
% 0.57/0.78          | ~ (r1_tarski @ X1 @ X2)
% 0.57/0.78          | (r1_tarski @ X0 @ X2))),
% 0.57/0.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.57/0.78  thf('15', plain,
% 0.57/0.78      (![X0 : $i]:
% 0.57/0.78         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 0.57/0.78          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.57/0.78      inference('sup-', [status(thm)], ['13', '14'])).
% 0.57/0.78  thf('16', plain,
% 0.57/0.78      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.57/0.78      inference('sup-', [status(thm)], ['8', '15'])).
% 0.57/0.78  thf('17', plain,
% 0.57/0.78      (![X4 : $i, X6 : $i]:
% 0.57/0.78         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.57/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.78  thf('18', plain,
% 0.57/0.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.57/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.57/0.78  thf('19', plain,
% 0.57/0.78      ((![X23 : $i]:
% 0.57/0.78          (((X23) = (k1_xboole_0))
% 0.57/0.78           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78           | ~ (r1_tarski @ X23 @ sk_B_1)))
% 0.57/0.78         <= ((![X23 : $i]:
% 0.57/0.78                (((X23) = (k1_xboole_0))
% 0.57/0.78                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78                 | ~ (r1_tarski @ X23 @ sk_B_1))))),
% 0.57/0.78      inference('split', [status(esa)], ['4'])).
% 0.57/0.78  thf('20', plain,
% 0.57/0.78      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.57/0.78         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.57/0.78         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.57/0.78         <= ((![X23 : $i]:
% 0.57/0.78                (((X23) = (k1_xboole_0))
% 0.57/0.78                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78                 | ~ (r1_tarski @ X23 @ sk_B_1))))),
% 0.57/0.78      inference('sup-', [status(thm)], ['18', '19'])).
% 0.57/0.78  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.57/0.78      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.78  thf('22', plain,
% 0.57/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf(fc9_tops_1, axiom,
% 0.57/0.78    (![A:$i,B:$i]:
% 0.57/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.57/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.78       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.57/0.78  thf('23', plain,
% 0.57/0.78      (![X13 : $i, X14 : $i]:
% 0.57/0.78         (~ (l1_pre_topc @ X13)
% 0.57/0.78          | ~ (v2_pre_topc @ X13)
% 0.57/0.78          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.57/0.78          | (v3_pre_topc @ (k1_tops_1 @ X13 @ X14) @ X13))),
% 0.57/0.78      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.57/0.78  thf('24', plain,
% 0.57/0.78      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.57/0.78        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.78        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.78  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.57/0.78      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.57/0.78  thf('28', plain,
% 0.57/0.78      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.57/0.78         <= ((![X23 : $i]:
% 0.57/0.78                (((X23) = (k1_xboole_0))
% 0.57/0.78                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78                 | ~ (r1_tarski @ X23 @ sk_B_1))))),
% 0.57/0.78      inference('demod', [status(thm)], ['20', '21', '27'])).
% 0.57/0.78  thf('29', plain,
% 0.57/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf(t84_tops_1, axiom,
% 0.57/0.78    (![A:$i]:
% 0.57/0.78     ( ( l1_pre_topc @ A ) =>
% 0.57/0.78       ( ![B:$i]:
% 0.57/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.78           ( ( v2_tops_1 @ B @ A ) <=>
% 0.57/0.78             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.57/0.78  thf('30', plain,
% 0.57/0.78      (![X21 : $i, X22 : $i]:
% 0.57/0.78         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.57/0.78          | ((k1_tops_1 @ X22 @ X21) != (k1_xboole_0))
% 0.57/0.78          | (v2_tops_1 @ X21 @ X22)
% 0.57/0.78          | ~ (l1_pre_topc @ X22))),
% 0.57/0.78      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.57/0.78  thf('31', plain,
% 0.57/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.57/0.78        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.57/0.78        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.78  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('33', plain,
% 0.57/0.78      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.57/0.78        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.57/0.78      inference('demod', [status(thm)], ['31', '32'])).
% 0.57/0.78  thf('34', plain,
% 0.57/0.78      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.57/0.78         <= ((![X23 : $i]:
% 0.57/0.78                (((X23) = (k1_xboole_0))
% 0.57/0.78                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78                 | ~ (r1_tarski @ X23 @ sk_B_1))))),
% 0.57/0.78      inference('sup-', [status(thm)], ['28', '33'])).
% 0.57/0.78  thf('35', plain,
% 0.57/0.78      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.57/0.78         <= ((![X23 : $i]:
% 0.57/0.78                (((X23) = (k1_xboole_0))
% 0.57/0.78                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78                 | ~ (r1_tarski @ X23 @ sk_B_1))))),
% 0.57/0.78      inference('simplify', [status(thm)], ['34'])).
% 0.57/0.78  thf('36', plain,
% 0.57/0.78      (((r1_tarski @ sk_C @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('37', plain,
% 0.57/0.78      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.57/0.78      inference('split', [status(esa)], ['36'])).
% 0.57/0.78  thf('38', plain,
% 0.57/0.78      (~
% 0.57/0.78       (![X23 : $i]:
% 0.57/0.78          (((X23) = (k1_xboole_0))
% 0.57/0.78           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.57/0.78           | ~ (r1_tarski @ X23 @ sk_B_1))) | 
% 0.57/0.78       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('sup-', [status(thm)], ['35', '37'])).
% 0.57/0.78  thf('39', plain,
% 0.57/0.78      (((r1_tarski @ sk_C @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('split', [status(esa)], ['36'])).
% 0.57/0.78  thf('40', plain,
% 0.57/0.78      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.57/0.78      inference('split', [status(esa)], ['4'])).
% 0.57/0.78  thf('41', plain,
% 0.57/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('42', plain,
% 0.57/0.78      (![X21 : $i, X22 : $i]:
% 0.57/0.78         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.57/0.78          | ~ (v2_tops_1 @ X21 @ X22)
% 0.57/0.78          | ((k1_tops_1 @ X22 @ X21) = (k1_xboole_0))
% 0.57/0.78          | ~ (l1_pre_topc @ X22))),
% 0.57/0.78      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.57/0.78  thf('43', plain,
% 0.57/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.57/0.78        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.57/0.78        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('sup-', [status(thm)], ['41', '42'])).
% 0.57/0.78  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('45', plain,
% 0.57/0.78      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.57/0.78        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.57/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.57/0.78  thf('46', plain,
% 0.57/0.78      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.57/0.78         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['40', '45'])).
% 0.57/0.78  thf(t29_mcart_1, axiom,
% 0.57/0.78    (![A:$i]:
% 0.57/0.78     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.57/0.78          ( ![B:$i]:
% 0.57/0.78            ( ~( ( r2_hidden @ B @ A ) & 
% 0.57/0.78                 ( ![C:$i,D:$i,E:$i]:
% 0.57/0.78                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.57/0.78                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.57/0.78  thf('47', plain,
% 0.57/0.78      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.57/0.78      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.57/0.78  thf('48', plain,
% 0.57/0.78      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.57/0.78      inference('split', [status(esa)], ['2'])).
% 0.57/0.78  thf('49', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.57/0.78      inference('sup-', [status(thm)], ['6', '7'])).
% 0.57/0.78  thf('50', plain,
% 0.57/0.78      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.57/0.78      inference('split', [status(esa)], ['36'])).
% 0.57/0.78  thf('51', plain,
% 0.57/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.78         (~ (r1_tarski @ X0 @ X1)
% 0.57/0.78          | ~ (r1_tarski @ X1 @ X2)
% 0.57/0.78          | (r1_tarski @ X0 @ X2))),
% 0.57/0.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.57/0.78  thf('52', plain,
% 0.57/0.78      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B_1 @ X0)))
% 0.57/0.78         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.57/0.78  thf('53', plain,
% 0.57/0.78      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.57/0.78         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['49', '52'])).
% 0.57/0.78  thf('54', plain,
% 0.57/0.78      (![X4 : $i, X6 : $i]:
% 0.57/0.78         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.57/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.78  thf('55', plain,
% 0.57/0.78      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.57/0.78         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.78  thf('56', plain,
% 0.57/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf(t54_tops_1, axiom,
% 0.57/0.78    (![A:$i]:
% 0.57/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.78       ( ![B:$i,C:$i]:
% 0.57/0.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.78           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.57/0.78             ( ?[D:$i]:
% 0.57/0.78               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.57/0.78                 ( v3_pre_topc @ D @ A ) & 
% 0.57/0.78                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.57/0.78  thf('57', plain,
% 0.57/0.78      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.78         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.57/0.78          | ~ (r2_hidden @ X19 @ X20)
% 0.57/0.78          | ~ (r1_tarski @ X20 @ X17)
% 0.57/0.78          | ~ (v3_pre_topc @ X20 @ X18)
% 0.57/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.57/0.78          | (r2_hidden @ X19 @ (k1_tops_1 @ X18 @ X17))
% 0.57/0.78          | ~ (l1_pre_topc @ X18)
% 0.57/0.78          | ~ (v2_pre_topc @ X18))),
% 0.57/0.78      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.57/0.78  thf('58', plain,
% 0.57/0.78      (![X0 : $i, X1 : $i]:
% 0.57/0.78         (~ (v2_pre_topc @ sk_A)
% 0.57/0.78          | ~ (l1_pre_topc @ sk_A)
% 0.57/0.78          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.57/0.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.57/0.78          | ~ (r1_tarski @ X1 @ sk_B_1)
% 0.57/0.78          | ~ (r2_hidden @ X0 @ X1))),
% 0.57/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.57/0.78  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.78  thf('61', plain,
% 0.57/0.78      (![X0 : $i, X1 : $i]:
% 0.57/0.78         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.57/0.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.78          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.57/0.78          | ~ (r1_tarski @ X1 @ sk_B_1)
% 0.57/0.78          | ~ (r2_hidden @ X0 @ X1))),
% 0.57/0.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.57/0.78  thf('62', plain,
% 0.57/0.78      ((![X0 : $i]:
% 0.57/0.78          (~ (r2_hidden @ X0 @ sk_C)
% 0.57/0.78           | ~ (r1_tarski @ sk_C @ sk_B_1)
% 0.57/0.78           | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.57/0.78           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.57/0.78         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['55', '61'])).
% 0.57/0.78  thf('63', plain,
% 0.57/0.78      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.57/0.78      inference('split', [status(esa)], ['36'])).
% 0.57/0.78  thf('64', plain,
% 0.57/0.78      ((![X0 : $i]:
% 0.57/0.78          (~ (r2_hidden @ X0 @ sk_C)
% 0.57/0.78           | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.57/0.78           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.57/0.78         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.57/0.78      inference('demod', [status(thm)], ['62', '63'])).
% 0.57/0.78  thf('65', plain,
% 0.57/0.78      ((![X0 : $i]:
% 0.57/0.78          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.57/0.78           | ~ (r2_hidden @ X0 @ sk_C)))
% 0.57/0.78         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['48', '64'])).
% 0.57/0.78  thf('66', plain,
% 0.57/0.78      (((((sk_C) = (k1_xboole_0))
% 0.57/0.78         | (r2_hidden @ (sk_B @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.57/0.78         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['47', '65'])).
% 0.57/0.78  thf(t7_ordinal1, axiom,
% 0.57/0.78    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.78  thf('67', plain,
% 0.57/0.78      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.57/0.78      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.57/0.78  thf('68', plain,
% 0.57/0.78      (((((sk_C) = (k1_xboole_0))
% 0.57/0.78         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_C))))
% 0.57/0.78         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['66', '67'])).
% 0.57/0.78  thf('69', plain,
% 0.57/0.78      (((~ (r1_tarski @ k1_xboole_0 @ (sk_B @ sk_C)) | ((sk_C) = (k1_xboole_0))))
% 0.57/0.78         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.57/0.78             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 0.57/0.78             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['46', '68'])).
% 0.57/0.78  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.57/0.78  thf('70', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.57/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.57/0.78  thf('71', plain,
% 0.57/0.78      ((((sk_C) = (k1_xboole_0)))
% 0.57/0.78         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.57/0.78             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 0.57/0.78             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.57/0.78      inference('demod', [status(thm)], ['69', '70'])).
% 0.57/0.78  thf('72', plain,
% 0.57/0.78      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.57/0.78      inference('split', [status(esa)], ['0'])).
% 0.57/0.78  thf('73', plain,
% 0.57/0.78      ((((sk_C) != (sk_C)))
% 0.57/0.78         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.57/0.78             ((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.57/0.78             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 0.57/0.78             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.57/0.78      inference('sup-', [status(thm)], ['71', '72'])).
% 0.57/0.78  thf('74', plain,
% 0.57/0.78      (~ ((r1_tarski @ sk_C @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.57/0.78       ~ ((v3_pre_topc @ sk_C @ sk_A)) | (((sk_C) = (k1_xboole_0)))),
% 0.57/0.78      inference('simplify', [status(thm)], ['73'])).
% 0.57/0.78  thf('75', plain, ($false),
% 0.57/0.78      inference('sat_resolution*', [status(thm)],
% 0.57/0.78                ['1', '3', '5', '38', '39', '74'])).
% 0.57/0.78  
% 0.57/0.78  % SZS output end Refutation
% 0.57/0.78  
% 0.57/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
