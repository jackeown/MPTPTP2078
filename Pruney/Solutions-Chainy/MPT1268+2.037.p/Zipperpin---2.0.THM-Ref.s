%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gqeBBfoWsq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:21 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 173 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  872 (2383 expanded)
%              Number of equality atoms :   35 (  91 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X25 @ sk_A )
      | ~ ( r1_tarski @ X25 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) )
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
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
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
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X15 @ X16 ) @ X15 ) ) ),
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
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ~ ! [X25: $i] :
          ( ( X25 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tops_1 @ X23 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('50',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('51',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( r1_tarski @ sk_B_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X19 )
      | ~ ( v3_pre_topc @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r2_hidden @ X21 @ ( k1_tops_1 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
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
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r1_tarski @ sk_C_1 @ sk_B_1 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','65'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('68',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_C_1 ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','68'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('70',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','38','39','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gqeBBfoWsq
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.86  % Solved by: fo/fo7.sh
% 0.65/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.86  % done 976 iterations in 0.423s
% 0.65/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.86  % SZS output start Refutation
% 0.65/0.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.65/0.86  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.65/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.65/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.65/0.86  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.65/0.86  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.65/0.86  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.65/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.65/0.86  thf(sk_B_type, type, sk_B: $i > $i).
% 0.65/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.86  thf(t86_tops_1, conjecture,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86           ( ( v2_tops_1 @ B @ A ) <=>
% 0.65/0.86             ( ![C:$i]:
% 0.65/0.86               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.65/0.86                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.65/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.86    (~( ![A:$i]:
% 0.65/0.86        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.86          ( ![B:$i]:
% 0.65/0.86            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86              ( ( v2_tops_1 @ B @ A ) <=>
% 0.65/0.86                ( ![C:$i]:
% 0.65/0.86                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.65/0.86                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.65/0.86    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.65/0.86  thf('0', plain,
% 0.65/0.86      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('1', plain,
% 0.65/0.86      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf('2', plain,
% 0.65/0.86      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('3', plain,
% 0.65/0.86      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('split', [status(esa)], ['2'])).
% 0.65/0.86  thf('4', plain,
% 0.65/0.86      (![X25 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86          | ((X25) = (k1_xboole_0))
% 0.65/0.86          | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86          | ~ (r1_tarski @ X25 @ sk_B_1)
% 0.65/0.86          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('5', plain,
% 0.65/0.86      ((![X25 : $i]:
% 0.65/0.86          (((X25) = (k1_xboole_0))
% 0.65/0.86           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86           | ~ (r1_tarski @ X25 @ sk_B_1))) | 
% 0.65/0.86       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('split', [status(esa)], ['4'])).
% 0.65/0.86  thf('6', plain,
% 0.65/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(t3_subset, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.65/0.86  thf('7', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i]:
% 0.65/0.86         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.86  thf('8', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.65/0.86  thf('9', plain,
% 0.65/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(t44_tops_1, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( l1_pre_topc @ A ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.65/0.86  thf('10', plain,
% 0.65/0.86      (![X17 : $i, X18 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.65/0.86          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ X17)
% 0.65/0.86          | ~ (l1_pre_topc @ X18))),
% 0.65/0.86      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.65/0.86  thf('11', plain,
% 0.65/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.86        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.65/0.86      inference('sup-', [status(thm)], ['9', '10'])).
% 0.65/0.86  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.65/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.65/0.86  thf(t1_xboole_1, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.65/0.86       ( r1_tarski @ A @ C ) ))).
% 0.65/0.86  thf('14', plain,
% 0.65/0.86      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.86         (~ (r1_tarski @ X1 @ X2)
% 0.65/0.86          | ~ (r1_tarski @ X2 @ X3)
% 0.65/0.86          | (r1_tarski @ X1 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.65/0.86  thf('15', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 0.65/0.86          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.65/0.86      inference('sup-', [status(thm)], ['13', '14'])).
% 0.65/0.86  thf('16', plain,
% 0.65/0.86      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['8', '15'])).
% 0.65/0.86  thf('17', plain,
% 0.65/0.86      (![X10 : $i, X12 : $i]:
% 0.65/0.86         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.65/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.86  thf('18', plain,
% 0.65/0.86      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['16', '17'])).
% 0.65/0.86  thf('19', plain,
% 0.65/0.86      ((![X25 : $i]:
% 0.65/0.86          (((X25) = (k1_xboole_0))
% 0.65/0.86           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86           | ~ (r1_tarski @ X25 @ sk_B_1)))
% 0.65/0.86         <= ((![X25 : $i]:
% 0.65/0.86                (((X25) = (k1_xboole_0))
% 0.65/0.86                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 0.65/0.86      inference('split', [status(esa)], ['4'])).
% 0.65/0.86  thf('20', plain,
% 0.65/0.86      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.65/0.86         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.65/0.86         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.65/0.86         <= ((![X25 : $i]:
% 0.65/0.86                (((X25) = (k1_xboole_0))
% 0.65/0.86                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['18', '19'])).
% 0.65/0.86  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.65/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.65/0.86  thf('22', plain,
% 0.65/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(fc9_tops_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.65/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.65/0.86       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.65/0.86  thf('23', plain,
% 0.65/0.86      (![X15 : $i, X16 : $i]:
% 0.65/0.86         (~ (l1_pre_topc @ X15)
% 0.65/0.86          | ~ (v2_pre_topc @ X15)
% 0.65/0.86          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.65/0.86          | (v3_pre_topc @ (k1_tops_1 @ X15 @ X16) @ X15))),
% 0.65/0.86      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.65/0.86  thf('24', plain,
% 0.65/0.86      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.65/0.86        | ~ (v2_pre_topc @ sk_A)
% 0.65/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['22', '23'])).
% 0.65/0.86  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.65/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.65/0.86  thf('28', plain,
% 0.65/0.86      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.65/0.86         <= ((![X25 : $i]:
% 0.65/0.86                (((X25) = (k1_xboole_0))
% 0.65/0.86                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 0.65/0.86      inference('demod', [status(thm)], ['20', '21', '27'])).
% 0.65/0.86  thf('29', plain,
% 0.65/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(t84_tops_1, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( l1_pre_topc @ A ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86           ( ( v2_tops_1 @ B @ A ) <=>
% 0.65/0.86             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.65/0.86  thf('30', plain,
% 0.65/0.86      (![X23 : $i, X24 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.65/0.86          | ((k1_tops_1 @ X24 @ X23) != (k1_xboole_0))
% 0.65/0.86          | (v2_tops_1 @ X23 @ X24)
% 0.65/0.86          | ~ (l1_pre_topc @ X24))),
% 0.65/0.86      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.65/0.86  thf('31', plain,
% 0.65/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.86        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.65/0.86        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['29', '30'])).
% 0.65/0.86  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('33', plain,
% 0.65/0.86      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.65/0.86        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.65/0.86      inference('demod', [status(thm)], ['31', '32'])).
% 0.65/0.86  thf('34', plain,
% 0.65/0.86      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.65/0.86         <= ((![X25 : $i]:
% 0.65/0.86                (((X25) = (k1_xboole_0))
% 0.65/0.86                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['28', '33'])).
% 0.65/0.86  thf('35', plain,
% 0.65/0.86      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.65/0.86         <= ((![X25 : $i]:
% 0.65/0.86                (((X25) = (k1_xboole_0))
% 0.65/0.86                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 0.65/0.86      inference('simplify', [status(thm)], ['34'])).
% 0.65/0.86  thf('36', plain,
% 0.65/0.86      (((r1_tarski @ sk_C_1 @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('37', plain,
% 0.65/0.86      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.65/0.86      inference('split', [status(esa)], ['36'])).
% 0.65/0.86  thf('38', plain,
% 0.65/0.86      (~
% 0.65/0.86       (![X25 : $i]:
% 0.65/0.86          (((X25) = (k1_xboole_0))
% 0.65/0.86           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.65/0.86           | ~ (r1_tarski @ X25 @ sk_B_1))) | 
% 0.65/0.86       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['35', '37'])).
% 0.65/0.86  thf('39', plain,
% 0.65/0.86      (((r1_tarski @ sk_C_1 @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('split', [status(esa)], ['36'])).
% 0.65/0.86  thf('40', plain,
% 0.65/0.86      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.65/0.86      inference('split', [status(esa)], ['4'])).
% 0.65/0.86  thf('41', plain,
% 0.65/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('42', plain,
% 0.65/0.86      (![X23 : $i, X24 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.65/0.86          | ~ (v2_tops_1 @ X23 @ X24)
% 0.65/0.86          | ((k1_tops_1 @ X24 @ X23) = (k1_xboole_0))
% 0.65/0.86          | ~ (l1_pre_topc @ X24))),
% 0.65/0.86      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.65/0.86  thf('43', plain,
% 0.65/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.86        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.65/0.86        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.65/0.86  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('45', plain,
% 0.65/0.86      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.65/0.86        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.65/0.86      inference('demod', [status(thm)], ['43', '44'])).
% 0.65/0.86  thf('46', plain,
% 0.65/0.86      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.65/0.86         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['40', '45'])).
% 0.65/0.86  thf(t7_xboole_0, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.65/0.86          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.65/0.86  thf('47', plain,
% 0.65/0.86      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.65/0.86  thf('48', plain,
% 0.65/0.86      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.86      inference('split', [status(esa)], ['2'])).
% 0.65/0.86  thf('49', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.65/0.86  thf('50', plain,
% 0.65/0.86      (((r1_tarski @ sk_C_1 @ sk_B_1)) <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 0.65/0.86      inference('split', [status(esa)], ['36'])).
% 0.65/0.86  thf('51', plain,
% 0.65/0.86      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.86         (~ (r1_tarski @ X1 @ X2)
% 0.65/0.86          | ~ (r1_tarski @ X2 @ X3)
% 0.65/0.86          | (r1_tarski @ X1 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.65/0.86  thf('52', plain,
% 0.65/0.86      ((![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ sk_B_1 @ X0)))
% 0.65/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['50', '51'])).
% 0.65/0.86  thf('53', plain,
% 0.65/0.86      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['49', '52'])).
% 0.65/0.86  thf('54', plain,
% 0.65/0.86      (![X10 : $i, X12 : $i]:
% 0.65/0.86         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.65/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.86  thf('55', plain,
% 0.65/0.86      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['53', '54'])).
% 0.65/0.86  thf('56', plain,
% 0.65/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(t54_tops_1, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.86       ( ![B:$i,C:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.65/0.86             ( ?[D:$i]:
% 0.65/0.86               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.65/0.86                 ( v3_pre_topc @ D @ A ) & 
% 0.65/0.86                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.65/0.86  thf('57', plain,
% 0.65/0.86      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.65/0.86          | ~ (r2_hidden @ X21 @ X22)
% 0.65/0.86          | ~ (r1_tarski @ X22 @ X19)
% 0.65/0.86          | ~ (v3_pre_topc @ X22 @ X20)
% 0.65/0.86          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.65/0.86          | (r2_hidden @ X21 @ (k1_tops_1 @ X20 @ X19))
% 0.65/0.86          | ~ (l1_pre_topc @ X20)
% 0.65/0.86          | ~ (v2_pre_topc @ X20))),
% 0.65/0.86      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.65/0.86  thf('58', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (~ (v2_pre_topc @ sk_A)
% 0.65/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.65/0.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.65/0.86          | ~ (r1_tarski @ X1 @ sk_B_1)
% 0.65/0.86          | ~ (r2_hidden @ X0 @ X1))),
% 0.65/0.86      inference('sup-', [status(thm)], ['56', '57'])).
% 0.65/0.86  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('61', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.65/0.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.65/0.86          | ~ (r1_tarski @ X1 @ sk_B_1)
% 0.65/0.86          | ~ (r2_hidden @ X0 @ X1))),
% 0.65/0.86      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.65/0.86  thf('62', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          (~ (r2_hidden @ X0 @ sk_C_1)
% 0.65/0.86           | ~ (r1_tarski @ sk_C_1 @ sk_B_1)
% 0.65/0.86           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.65/0.86           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.65/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['55', '61'])).
% 0.65/0.86  thf('63', plain,
% 0.65/0.86      (((r1_tarski @ sk_C_1 @ sk_B_1)) <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 0.65/0.86      inference('split', [status(esa)], ['36'])).
% 0.65/0.86  thf('64', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          (~ (r2_hidden @ X0 @ sk_C_1)
% 0.65/0.86           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.65/0.86           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.65/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 0.65/0.86      inference('demod', [status(thm)], ['62', '63'])).
% 0.65/0.86  thf('65', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.65/0.86           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.65/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B_1)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['48', '64'])).
% 0.65/0.86  thf('66', plain,
% 0.65/0.86      (((((sk_C_1) = (k1_xboole_0))
% 0.65/0.86         | (r2_hidden @ (sk_B @ sk_C_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.65/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B_1)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['47', '65'])).
% 0.65/0.86  thf(t7_ordinal1, axiom,
% 0.65/0.86    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.65/0.86  thf('67', plain,
% 0.65/0.86      (![X13 : $i, X14 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.65/0.86      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.65/0.86  thf('68', plain,
% 0.65/0.86      (((((sk_C_1) = (k1_xboole_0))
% 0.65/0.86         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_C_1))))
% 0.65/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B_1)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['66', '67'])).
% 0.65/0.86  thf('69', plain,
% 0.65/0.86      (((~ (r1_tarski @ k1_xboole_0 @ (sk_B @ sk_C_1))
% 0.65/0.86         | ((sk_C_1) = (k1_xboole_0))))
% 0.65/0.86         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.65/0.86             ((r1_tarski @ sk_C_1 @ sk_B_1)) & 
% 0.65/0.86             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['46', '68'])).
% 0.65/0.86  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.65/0.86  thf('70', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.65/0.86      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.65/0.86  thf('71', plain,
% 0.65/0.86      ((((sk_C_1) = (k1_xboole_0)))
% 0.65/0.86         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.65/0.86             ((r1_tarski @ sk_C_1 @ sk_B_1)) & 
% 0.65/0.86             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.86      inference('demod', [status(thm)], ['69', '70'])).
% 0.65/0.86  thf('72', plain,
% 0.65/0.86      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.65/0.86      inference('split', [status(esa)], ['0'])).
% 0.65/0.86  thf('73', plain,
% 0.65/0.86      ((((sk_C_1) != (sk_C_1)))
% 0.65/0.86         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 0.65/0.86             ((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.65/0.86             ((r1_tarski @ sk_C_1 @ sk_B_1)) & 
% 0.65/0.86             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['71', '72'])).
% 0.65/0.86  thf('74', plain,
% 0.65/0.86      (~ ((r1_tarski @ sk_C_1 @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.65/0.86       ~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | (((sk_C_1) = (k1_xboole_0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['73'])).
% 0.65/0.86  thf('75', plain, ($false),
% 0.65/0.86      inference('sat_resolution*', [status(thm)],
% 0.65/0.86                ['1', '3', '5', '38', '39', '74'])).
% 0.65/0.86  
% 0.65/0.86  % SZS output end Refutation
% 0.65/0.86  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
