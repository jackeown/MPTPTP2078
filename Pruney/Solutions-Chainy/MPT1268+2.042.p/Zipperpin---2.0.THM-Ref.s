%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hhyG5goVb7

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:22 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 184 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   20
%              Number of atoms          :  953 (2500 expanded)
%              Number of equality atoms :   32 (  88 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X24 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( r1_tarski @ X24 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('24',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
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
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_tops_1 @ X23 @ X22 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ~ ! [X24: $i] :
          ( ( X24 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X24 @ sk_A )
          | ~ ( r1_tarski @ X24 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('40',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tops_1 @ X22 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X22 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X18 )
      | ~ ( v3_pre_topc @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r1_tarski @ sk_C_1 @ sk_B )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','72'])).

thf('74',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','76'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('78',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('79',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','38','39','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hhyG5goVb7
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.65/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.65/0.85  % Solved by: fo/fo7.sh
% 0.65/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.85  % done 989 iterations in 0.381s
% 0.65/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.65/0.85  % SZS output start Refutation
% 0.65/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.65/0.85  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.65/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.65/0.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.65/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.85  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.65/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.65/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.65/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.65/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.85  thf(t86_tops_1, conjecture,
% 0.65/0.85    (![A:$i]:
% 0.65/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.85       ( ![B:$i]:
% 0.65/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.85           ( ( v2_tops_1 @ B @ A ) <=>
% 0.65/0.85             ( ![C:$i]:
% 0.65/0.85               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.85                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.65/0.85                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.65/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.85    (~( ![A:$i]:
% 0.65/0.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.85          ( ![B:$i]:
% 0.65/0.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.85              ( ( v2_tops_1 @ B @ A ) <=>
% 0.65/0.85                ( ![C:$i]:
% 0.65/0.85                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.85                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.65/0.85                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.65/0.85    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.65/0.85  thf('0', plain,
% 0.65/0.85      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('1', plain,
% 0.65/0.85      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('split', [status(esa)], ['0'])).
% 0.65/0.85  thf('2', plain,
% 0.65/0.85      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('3', plain,
% 0.65/0.85      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('split', [status(esa)], ['2'])).
% 0.65/0.85  thf('4', plain,
% 0.65/0.85      (![X24 : $i]:
% 0.65/0.85         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85          | ((X24) = (k1_xboole_0))
% 0.65/0.85          | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85          | ~ (r1_tarski @ X24 @ sk_B)
% 0.65/0.85          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('5', plain,
% 0.65/0.85      ((![X24 : $i]:
% 0.65/0.85          (((X24) = (k1_xboole_0))
% 0.65/0.85           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85           | ~ (r1_tarski @ X24 @ sk_B))) | 
% 0.65/0.85       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('split', [status(esa)], ['4'])).
% 0.65/0.85  thf('6', plain,
% 0.65/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf(t3_subset, axiom,
% 0.65/0.85    (![A:$i,B:$i]:
% 0.65/0.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.65/0.85  thf('7', plain,
% 0.65/0.85      (![X9 : $i, X10 : $i]:
% 0.65/0.85         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.65/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.85  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.65/0.85  thf('9', plain,
% 0.65/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf(t44_tops_1, axiom,
% 0.65/0.85    (![A:$i]:
% 0.65/0.85     ( ( l1_pre_topc @ A ) =>
% 0.65/0.85       ( ![B:$i]:
% 0.65/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.85           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.65/0.85  thf('10', plain,
% 0.65/0.85      (![X16 : $i, X17 : $i]:
% 0.65/0.85         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.65/0.85          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.65/0.85          | ~ (l1_pre_topc @ X17))),
% 0.65/0.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.65/0.85  thf('11', plain,
% 0.65/0.85      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.65/0.85      inference('sup-', [status(thm)], ['9', '10'])).
% 0.65/0.85  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.65/0.85      inference('demod', [status(thm)], ['11', '12'])).
% 0.65/0.85  thf(t1_xboole_1, axiom,
% 0.65/0.85    (![A:$i,B:$i,C:$i]:
% 0.65/0.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.65/0.85       ( r1_tarski @ A @ C ) ))).
% 0.65/0.85  thf('14', plain,
% 0.65/0.85      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.65/0.85         (~ (r1_tarski @ X4 @ X5)
% 0.65/0.85          | ~ (r1_tarski @ X5 @ X6)
% 0.65/0.85          | (r1_tarski @ X4 @ X6))),
% 0.65/0.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.65/0.85  thf('15', plain,
% 0.65/0.85      (![X0 : $i]:
% 0.65/0.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.65/0.85          | ~ (r1_tarski @ sk_B @ X0))),
% 0.65/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.65/0.85  thf('16', plain,
% 0.65/0.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.65/0.85      inference('sup-', [status(thm)], ['8', '15'])).
% 0.65/0.85  thf('17', plain,
% 0.65/0.85      (![X9 : $i, X11 : $i]:
% 0.65/0.85         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.65/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.85  thf('18', plain,
% 0.65/0.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.65/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['16', '17'])).
% 0.65/0.85  thf('19', plain,
% 0.65/0.85      ((![X24 : $i]:
% 0.65/0.85          (((X24) = (k1_xboole_0))
% 0.65/0.85           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85           | ~ (r1_tarski @ X24 @ sk_B)))
% 0.65/0.85         <= ((![X24 : $i]:
% 0.65/0.85                (((X24) = (k1_xboole_0))
% 0.65/0.85                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.65/0.85      inference('split', [status(esa)], ['4'])).
% 0.65/0.85  thf('20', plain,
% 0.65/0.85      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.65/0.85         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.65/0.85         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.65/0.85         <= ((![X24 : $i]:
% 0.65/0.85                (((X24) = (k1_xboole_0))
% 0.65/0.85                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.65/0.85      inference('sup-', [status(thm)], ['18', '19'])).
% 0.65/0.85  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.65/0.85      inference('demod', [status(thm)], ['11', '12'])).
% 0.65/0.85  thf('22', plain,
% 0.65/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf(fc9_tops_1, axiom,
% 0.65/0.85    (![A:$i,B:$i]:
% 0.65/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.65/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.65/0.85       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.65/0.85  thf('23', plain,
% 0.65/0.85      (![X14 : $i, X15 : $i]:
% 0.65/0.85         (~ (l1_pre_topc @ X14)
% 0.65/0.85          | ~ (v2_pre_topc @ X14)
% 0.65/0.85          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.65/0.85          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 0.65/0.85      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.65/0.85  thf('24', plain,
% 0.65/0.85      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.65/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.65/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.65/0.85      inference('sup-', [status(thm)], ['22', '23'])).
% 0.65/0.85  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.65/0.85      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.65/0.85  thf('28', plain,
% 0.65/0.85      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.65/0.85         <= ((![X24 : $i]:
% 0.65/0.85                (((X24) = (k1_xboole_0))
% 0.65/0.85                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.65/0.85      inference('demod', [status(thm)], ['20', '21', '27'])).
% 0.65/0.85  thf('29', plain,
% 0.65/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf(t84_tops_1, axiom,
% 0.65/0.85    (![A:$i]:
% 0.65/0.85     ( ( l1_pre_topc @ A ) =>
% 0.65/0.85       ( ![B:$i]:
% 0.65/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.85           ( ( v2_tops_1 @ B @ A ) <=>
% 0.65/0.85             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.65/0.85  thf('30', plain,
% 0.65/0.85      (![X22 : $i, X23 : $i]:
% 0.65/0.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.65/0.85          | ((k1_tops_1 @ X23 @ X22) != (k1_xboole_0))
% 0.65/0.85          | (v2_tops_1 @ X22 @ X23)
% 0.65/0.85          | ~ (l1_pre_topc @ X23))),
% 0.65/0.85      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.65/0.85  thf('31', plain,
% 0.65/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.85        | (v2_tops_1 @ sk_B @ sk_A)
% 0.65/0.85        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.65/0.85  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('33', plain,
% 0.65/0.85      (((v2_tops_1 @ sk_B @ sk_A)
% 0.65/0.85        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.65/0.85      inference('demod', [status(thm)], ['31', '32'])).
% 0.65/0.85  thf('34', plain,
% 0.65/0.85      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.65/0.85         <= ((![X24 : $i]:
% 0.65/0.85                (((X24) = (k1_xboole_0))
% 0.65/0.85                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.65/0.85      inference('sup-', [status(thm)], ['28', '33'])).
% 0.65/0.85  thf('35', plain,
% 0.65/0.85      (((v2_tops_1 @ sk_B @ sk_A))
% 0.65/0.85         <= ((![X24 : $i]:
% 0.65/0.85                (((X24) = (k1_xboole_0))
% 0.65/0.85                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.65/0.85      inference('simplify', [status(thm)], ['34'])).
% 0.65/0.85  thf('36', plain,
% 0.65/0.85      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('37', plain,
% 0.65/0.85      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.65/0.85      inference('split', [status(esa)], ['36'])).
% 0.65/0.85  thf('38', plain,
% 0.65/0.85      (~
% 0.65/0.85       (![X24 : $i]:
% 0.65/0.85          (((X24) = (k1_xboole_0))
% 0.65/0.85           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.65/0.85           | ~ (r1_tarski @ X24 @ sk_B))) | 
% 0.65/0.85       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('sup-', [status(thm)], ['35', '37'])).
% 0.65/0.85  thf('39', plain,
% 0.65/0.85      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('split', [status(esa)], ['36'])).
% 0.65/0.85  thf('40', plain,
% 0.65/0.85      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.65/0.85      inference('split', [status(esa)], ['4'])).
% 0.65/0.85  thf('41', plain,
% 0.65/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('42', plain,
% 0.65/0.85      (![X22 : $i, X23 : $i]:
% 0.65/0.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.65/0.85          | ~ (v2_tops_1 @ X22 @ X23)
% 0.65/0.85          | ((k1_tops_1 @ X23 @ X22) = (k1_xboole_0))
% 0.65/0.85          | ~ (l1_pre_topc @ X23))),
% 0.65/0.85      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.65/0.85  thf('43', plain,
% 0.65/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.85        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.65/0.85        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('sup-', [status(thm)], ['41', '42'])).
% 0.65/0.85  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('45', plain,
% 0.65/0.85      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.65/0.85        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.65/0.85      inference('demod', [status(thm)], ['43', '44'])).
% 0.65/0.85  thf('46', plain,
% 0.65/0.85      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.65/0.85         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['40', '45'])).
% 0.65/0.85  thf(d3_tarski, axiom,
% 0.65/0.85    (![A:$i,B:$i]:
% 0.65/0.85     ( ( r1_tarski @ A @ B ) <=>
% 0.65/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.65/0.85  thf('47', plain,
% 0.65/0.85      (![X1 : $i, X3 : $i]:
% 0.65/0.85         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.65/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.65/0.85  thf('48', plain,
% 0.65/0.85      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.85      inference('split', [status(esa)], ['2'])).
% 0.65/0.85  thf('49', plain,
% 0.65/0.85      (![X1 : $i, X3 : $i]:
% 0.65/0.85         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.65/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.65/0.85  thf('50', plain,
% 0.65/0.85      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('split', [status(esa)], ['36'])).
% 0.65/0.85  thf('51', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.85         (~ (r2_hidden @ X0 @ X1)
% 0.65/0.85          | (r2_hidden @ X0 @ X2)
% 0.65/0.85          | ~ (r1_tarski @ X1 @ X2))),
% 0.65/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.65/0.85  thf('52', plain,
% 0.65/0.85      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['50', '51'])).
% 0.65/0.85  thf('53', plain,
% 0.65/0.85      ((![X0 : $i]:
% 0.65/0.85          ((r1_tarski @ sk_C_1 @ X0)
% 0.65/0.85           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['49', '52'])).
% 0.65/0.85  thf('54', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.65/0.85  thf('55', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.85         (~ (r2_hidden @ X0 @ X1)
% 0.65/0.85          | (r2_hidden @ X0 @ X2)
% 0.65/0.85          | ~ (r1_tarski @ X1 @ X2))),
% 0.65/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.65/0.85  thf('56', plain,
% 0.65/0.85      (![X0 : $i]:
% 0.65/0.85         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.65/0.85      inference('sup-', [status(thm)], ['54', '55'])).
% 0.65/0.85  thf('57', plain,
% 0.65/0.85      ((![X0 : $i]:
% 0.65/0.85          ((r1_tarski @ sk_C_1 @ X0)
% 0.65/0.85           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_A))))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['53', '56'])).
% 0.65/0.85  thf('58', plain,
% 0.65/0.85      (![X1 : $i, X3 : $i]:
% 0.65/0.85         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.65/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.65/0.85  thf('59', plain,
% 0.65/0.85      ((((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.65/0.85         | (r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['57', '58'])).
% 0.65/0.85  thf('60', plain,
% 0.65/0.85      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('simplify', [status(thm)], ['59'])).
% 0.65/0.85  thf('61', plain,
% 0.65/0.85      (![X9 : $i, X11 : $i]:
% 0.65/0.85         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.65/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.85  thf('62', plain,
% 0.65/0.85      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['60', '61'])).
% 0.65/0.85  thf('63', plain,
% 0.65/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf(t54_tops_1, axiom,
% 0.65/0.85    (![A:$i]:
% 0.65/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.85       ( ![B:$i,C:$i]:
% 0.65/0.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.85           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.65/0.85             ( ?[D:$i]:
% 0.65/0.85               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.65/0.85                 ( v3_pre_topc @ D @ A ) & 
% 0.65/0.85                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.65/0.85  thf('64', plain,
% 0.65/0.85      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.65/0.85         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.65/0.85          | ~ (r2_hidden @ X20 @ X21)
% 0.65/0.85          | ~ (r1_tarski @ X21 @ X18)
% 0.65/0.85          | ~ (v3_pre_topc @ X21 @ X19)
% 0.65/0.85          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.65/0.85          | (r2_hidden @ X20 @ (k1_tops_1 @ X19 @ X18))
% 0.65/0.85          | ~ (l1_pre_topc @ X19)
% 0.65/0.85          | ~ (v2_pre_topc @ X19))),
% 0.65/0.85      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.65/0.85  thf('65', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         (~ (v2_pre_topc @ sk_A)
% 0.65/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.65/0.85          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.65/0.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.65/0.85          | ~ (r1_tarski @ X1 @ sk_B)
% 0.65/0.85          | ~ (r2_hidden @ X0 @ X1))),
% 0.65/0.85      inference('sup-', [status(thm)], ['63', '64'])).
% 0.65/0.85  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.85  thf('68', plain,
% 0.65/0.85      (![X0 : $i, X1 : $i]:
% 0.65/0.85         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.65/0.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.85          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.65/0.85          | ~ (r1_tarski @ X1 @ sk_B)
% 0.65/0.85          | ~ (r2_hidden @ X0 @ X1))),
% 0.65/0.85      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.65/0.85  thf('69', plain,
% 0.65/0.85      ((![X0 : $i]:
% 0.65/0.85          (~ (r2_hidden @ X0 @ sk_C_1)
% 0.65/0.85           | ~ (r1_tarski @ sk_C_1 @ sk_B)
% 0.65/0.85           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.65/0.85           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['62', '68'])).
% 0.65/0.85  thf('70', plain,
% 0.65/0.85      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('split', [status(esa)], ['36'])).
% 0.65/0.85  thf('71', plain,
% 0.65/0.85      ((![X0 : $i]:
% 0.65/0.85          (~ (r2_hidden @ X0 @ sk_C_1)
% 0.65/0.85           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.65/0.85           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.65/0.85      inference('demod', [status(thm)], ['69', '70'])).
% 0.65/0.85  thf('72', plain,
% 0.65/0.85      ((![X0 : $i]:
% 0.65/0.85          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.65/0.85           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['48', '71'])).
% 0.65/0.85  thf('73', plain,
% 0.65/0.85      ((![X0 : $i]:
% 0.65/0.85          ((r1_tarski @ sk_C_1 @ X0)
% 0.65/0.85           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['47', '72'])).
% 0.65/0.85  thf('74', plain,
% 0.65/0.85      (![X1 : $i, X3 : $i]:
% 0.65/0.85         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.65/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.65/0.85  thf('75', plain,
% 0.65/0.85      ((((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.65/0.85         | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['73', '74'])).
% 0.65/0.85  thf('76', plain,
% 0.65/0.85      (((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.65/0.85         <= (((r1_tarski @ sk_C_1 @ sk_B)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.85      inference('simplify', [status(thm)], ['75'])).
% 0.65/0.85  thf('77', plain,
% 0.65/0.85      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 0.65/0.85         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.65/0.85             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.65/0.85             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.85      inference('sup+', [status(thm)], ['46', '76'])).
% 0.65/0.85  thf(t3_xboole_1, axiom,
% 0.65/0.85    (![A:$i]:
% 0.65/0.85     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.65/0.85  thf('78', plain,
% 0.65/0.85      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.65/0.85      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.65/0.85  thf('79', plain,
% 0.65/0.85      ((((sk_C_1) = (k1_xboole_0)))
% 0.65/0.85         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.65/0.85             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.65/0.85             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['77', '78'])).
% 0.65/0.85  thf('80', plain,
% 0.65/0.85      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.65/0.85      inference('split', [status(esa)], ['0'])).
% 0.65/0.85  thf('81', plain,
% 0.65/0.85      ((((sk_C_1) != (sk_C_1)))
% 0.65/0.85         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 0.65/0.85             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.65/0.85             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.65/0.85             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.65/0.85      inference('sup-', [status(thm)], ['79', '80'])).
% 0.65/0.85  thf('82', plain,
% 0.65/0.85      (~ ((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.65/0.85       ~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | (((sk_C_1) = (k1_xboole_0)))),
% 0.65/0.85      inference('simplify', [status(thm)], ['81'])).
% 0.65/0.85  thf('83', plain, ($false),
% 0.65/0.85      inference('sat_resolution*', [status(thm)],
% 0.65/0.85                ['1', '3', '5', '38', '39', '82'])).
% 0.65/0.85  
% 0.65/0.85  % SZS output end Refutation
% 0.65/0.85  
% 0.65/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
