%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VQoxXCo0RB

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:22 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 181 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   19
%              Number of atoms          :  947 (2476 expanded)
%              Number of equality atoms :   32 (  88 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X26 @ sk_A )
      | ~ ( r1_tarski @ X26 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X26: $i] :
        ( ( X26 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_B ) )
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
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X26: $i] :
        ( ( X26 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_B ) )
   <= ! [X26: $i] :
        ( ( X26 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X26: $i] :
        ( ( X26 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_B ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
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
   <= ! [X26: $i] :
        ( ( X26 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_B ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
   <= ! [X26: $i] :
        ( ( X26 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X26: $i] :
        ( ( X26 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_B ) ) ),
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
    ( ~ ! [X26: $i] :
          ( ( X26 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_B ) )
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tops_1 @ X24 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('50',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X20 )
      | ~ ( v3_pre_topc @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r2_hidden @ X22 @ ( k1_tops_1 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
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
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r1_tarski @ sk_C_1 @ sk_B )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','69'])).

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('73',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_C_1 @ X0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(t49_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('76',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','38','39','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VQoxXCo0RB
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.77  % Solved by: fo/fo7.sh
% 0.57/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.77  % done 932 iterations in 0.318s
% 0.57/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.77  % SZS output start Refutation
% 0.57/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.57/0.77  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.57/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.57/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.77  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.57/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.57/0.77  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.57/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.57/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.77  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.57/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.77  thf(t86_tops_1, conjecture,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77           ( ( v2_tops_1 @ B @ A ) <=>
% 0.57/0.77             ( ![C:$i]:
% 0.57/0.77               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.57/0.77                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.57/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.77    (~( ![A:$i]:
% 0.57/0.77        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.77          ( ![B:$i]:
% 0.57/0.77            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77              ( ( v2_tops_1 @ B @ A ) <=>
% 0.57/0.77                ( ![C:$i]:
% 0.57/0.77                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.57/0.77                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.57/0.77    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.57/0.77  thf('0', plain,
% 0.57/0.77      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('1', plain,
% 0.57/0.77      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('split', [status(esa)], ['0'])).
% 0.57/0.77  thf('2', plain,
% 0.57/0.77      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('3', plain,
% 0.57/0.77      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('split', [status(esa)], ['2'])).
% 0.57/0.77  thf('4', plain,
% 0.57/0.77      (![X26 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77          | ((X26) = (k1_xboole_0))
% 0.57/0.77          | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77          | ~ (r1_tarski @ X26 @ sk_B)
% 0.57/0.77          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('5', plain,
% 0.57/0.77      ((![X26 : $i]:
% 0.57/0.77          (((X26) = (k1_xboole_0))
% 0.57/0.77           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77           | ~ (r1_tarski @ X26 @ sk_B))) | 
% 0.57/0.77       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('split', [status(esa)], ['4'])).
% 0.57/0.77  thf('6', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(t3_subset, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.77  thf('7', plain,
% 0.57/0.77      (![X8 : $i, X9 : $i]:
% 0.57/0.77         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.77  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.57/0.77  thf('9', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(t44_tops_1, axiom,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( l1_pre_topc @ A ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.57/0.77  thf('10', plain,
% 0.57/0.77      (![X18 : $i, X19 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.57/0.77          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 0.57/0.77          | ~ (l1_pre_topc @ X19))),
% 0.57/0.77      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.57/0.77  thf('11', plain,
% 0.57/0.77      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['9', '10'])).
% 0.57/0.77  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.57/0.77      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.77  thf(t1_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.57/0.77       ( r1_tarski @ A @ C ) ))).
% 0.57/0.77  thf('14', plain,
% 0.57/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X4 @ X5)
% 0.57/0.77          | ~ (r1_tarski @ X5 @ X6)
% 0.57/0.77          | (r1_tarski @ X4 @ X6))),
% 0.57/0.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.57/0.77  thf('15', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.57/0.77          | ~ (r1_tarski @ sk_B @ X0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['13', '14'])).
% 0.57/0.77  thf('16', plain,
% 0.57/0.77      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['8', '15'])).
% 0.57/0.77  thf('17', plain,
% 0.57/0.77      (![X8 : $i, X10 : $i]:
% 0.57/0.77         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.57/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.77  thf('18', plain,
% 0.57/0.77      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.57/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.57/0.77  thf('19', plain,
% 0.57/0.77      ((![X26 : $i]:
% 0.57/0.77          (((X26) = (k1_xboole_0))
% 0.57/0.77           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77           | ~ (r1_tarski @ X26 @ sk_B)))
% 0.57/0.77         <= ((![X26 : $i]:
% 0.57/0.77                (((X26) = (k1_xboole_0))
% 0.57/0.77                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77                 | ~ (r1_tarski @ X26 @ sk_B))))),
% 0.57/0.77      inference('split', [status(esa)], ['4'])).
% 0.57/0.77  thf('20', plain,
% 0.57/0.77      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.57/0.77         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.57/0.77         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.57/0.77         <= ((![X26 : $i]:
% 0.57/0.77                (((X26) = (k1_xboole_0))
% 0.57/0.77                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77                 | ~ (r1_tarski @ X26 @ sk_B))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.57/0.77  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.57/0.77      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.77  thf('22', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(fc9_tops_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.57/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.57/0.77  thf('23', plain,
% 0.57/0.77      (![X16 : $i, X17 : $i]:
% 0.57/0.77         (~ (l1_pre_topc @ X16)
% 0.57/0.77          | ~ (v2_pre_topc @ X16)
% 0.57/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.57/0.77          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 0.57/0.77      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.57/0.77  thf('24', plain,
% 0.57/0.77      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.57/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.77        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.77  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.57/0.77      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.57/0.77  thf('28', plain,
% 0.57/0.77      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((![X26 : $i]:
% 0.57/0.77                (((X26) = (k1_xboole_0))
% 0.57/0.77                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77                 | ~ (r1_tarski @ X26 @ sk_B))))),
% 0.57/0.77      inference('demod', [status(thm)], ['20', '21', '27'])).
% 0.57/0.77  thf('29', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(t84_tops_1, axiom,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( l1_pre_topc @ A ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77           ( ( v2_tops_1 @ B @ A ) <=>
% 0.57/0.77             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.57/0.77  thf('30', plain,
% 0.57/0.77      (![X24 : $i, X25 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.57/0.77          | ((k1_tops_1 @ X25 @ X24) != (k1_xboole_0))
% 0.57/0.77          | (v2_tops_1 @ X24 @ X25)
% 0.57/0.77          | ~ (l1_pre_topc @ X25))),
% 0.57/0.77      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.57/0.77  thf('31', plain,
% 0.57/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.57/0.77        | (v2_tops_1 @ sk_B @ sk_A)
% 0.57/0.77        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.77  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('33', plain,
% 0.57/0.77      (((v2_tops_1 @ sk_B @ sk_A)
% 0.57/0.77        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['31', '32'])).
% 0.57/0.77  thf('34', plain,
% 0.57/0.77      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.57/0.77         <= ((![X26 : $i]:
% 0.57/0.77                (((X26) = (k1_xboole_0))
% 0.57/0.77                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77                 | ~ (r1_tarski @ X26 @ sk_B))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['28', '33'])).
% 0.57/0.77  thf('35', plain,
% 0.57/0.77      (((v2_tops_1 @ sk_B @ sk_A))
% 0.57/0.77         <= ((![X26 : $i]:
% 0.57/0.77                (((X26) = (k1_xboole_0))
% 0.57/0.77                 | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77                 | ~ (r1_tarski @ X26 @ sk_B))))),
% 0.57/0.77      inference('simplify', [status(thm)], ['34'])).
% 0.57/0.77  thf('36', plain,
% 0.57/0.77      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('37', plain,
% 0.57/0.77      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.57/0.77      inference('split', [status(esa)], ['36'])).
% 0.57/0.77  thf('38', plain,
% 0.57/0.77      (~
% 0.57/0.77       (![X26 : $i]:
% 0.57/0.77          (((X26) = (k1_xboole_0))
% 0.57/0.77           | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.57/0.77           | ~ (r1_tarski @ X26 @ sk_B))) | 
% 0.57/0.77       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['35', '37'])).
% 0.57/0.77  thf('39', plain,
% 0.57/0.77      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('split', [status(esa)], ['36'])).
% 0.57/0.77  thf('40', plain,
% 0.57/0.77      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.57/0.77      inference('split', [status(esa)], ['4'])).
% 0.57/0.77  thf('41', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('42', plain,
% 0.57/0.77      (![X24 : $i, X25 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.57/0.77          | ~ (v2_tops_1 @ X24 @ X25)
% 0.57/0.77          | ((k1_tops_1 @ X25 @ X24) = (k1_xboole_0))
% 0.57/0.77          | ~ (l1_pre_topc @ X25))),
% 0.57/0.77      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.57/0.77  thf('43', plain,
% 0.57/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.57/0.77        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.57/0.77        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['41', '42'])).
% 0.57/0.77  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('45', plain,
% 0.57/0.77      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.57/0.77        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.57/0.77      inference('demod', [status(thm)], ['43', '44'])).
% 0.57/0.77  thf('46', plain,
% 0.57/0.77      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['40', '45'])).
% 0.57/0.77  thf(d3_tarski, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.77  thf('47', plain,
% 0.57/0.77      (![X1 : $i, X3 : $i]:
% 0.57/0.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.77  thf('48', plain,
% 0.57/0.77      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('split', [status(esa)], ['2'])).
% 0.57/0.77  thf('49', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.57/0.77  thf('50', plain,
% 0.57/0.77      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.57/0.77      inference('split', [status(esa)], ['36'])).
% 0.57/0.77  thf('51', plain,
% 0.57/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X4 @ X5)
% 0.57/0.77          | ~ (r1_tarski @ X5 @ X6)
% 0.57/0.77          | (r1_tarski @ X4 @ X6))),
% 0.57/0.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.57/0.77  thf('52', plain,
% 0.57/0.77      ((![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['50', '51'])).
% 0.57/0.77  thf('53', plain,
% 0.57/0.77      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['49', '52'])).
% 0.57/0.77  thf('54', plain,
% 0.57/0.77      (![X8 : $i, X10 : $i]:
% 0.57/0.77         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.57/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.77  thf('55', plain,
% 0.57/0.77      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.77  thf('56', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(t54_tops_1, axiom,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.77       ( ![B:$i,C:$i]:
% 0.57/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.57/0.77             ( ?[D:$i]:
% 0.57/0.77               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.57/0.77                 ( v3_pre_topc @ D @ A ) & 
% 0.57/0.77                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.57/0.77  thf('57', plain,
% 0.57/0.77      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.57/0.77          | ~ (r2_hidden @ X22 @ X23)
% 0.57/0.77          | ~ (r1_tarski @ X23 @ X20)
% 0.57/0.77          | ~ (v3_pre_topc @ X23 @ X21)
% 0.57/0.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.57/0.77          | (r2_hidden @ X22 @ (k1_tops_1 @ X21 @ X20))
% 0.57/0.77          | ~ (l1_pre_topc @ X21)
% 0.57/0.77          | ~ (v2_pre_topc @ X21))),
% 0.57/0.77      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.57/0.77  thf('58', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (~ (v2_pre_topc @ sk_A)
% 0.57/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.57/0.77          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.57/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.57/0.77          | ~ (r1_tarski @ X1 @ sk_B)
% 0.57/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.57/0.77      inference('sup-', [status(thm)], ['56', '57'])).
% 0.57/0.77  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('61', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.57/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.77          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.57/0.77          | ~ (r1_tarski @ X1 @ sk_B)
% 0.57/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.57/0.77      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.57/0.77  thf('62', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          (~ (r2_hidden @ X0 @ sk_C_1)
% 0.57/0.77           | ~ (r1_tarski @ sk_C_1 @ sk_B)
% 0.57/0.77           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.57/0.77           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['55', '61'])).
% 0.57/0.77  thf('63', plain,
% 0.57/0.77      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.57/0.77      inference('split', [status(esa)], ['36'])).
% 0.57/0.77  thf('64', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          (~ (r2_hidden @ X0 @ sk_C_1)
% 0.57/0.77           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.57/0.77           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.57/0.77      inference('demod', [status(thm)], ['62', '63'])).
% 0.57/0.77  thf('65', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.57/0.77           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['48', '64'])).
% 0.57/0.77  thf('66', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          ((r1_tarski @ sk_C_1 @ X0)
% 0.57/0.77           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['47', '65'])).
% 0.57/0.77  thf('67', plain,
% 0.57/0.77      (![X1 : $i, X3 : $i]:
% 0.57/0.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.57/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.77  thf('68', plain,
% 0.57/0.77      ((((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.57/0.77         | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['66', '67'])).
% 0.57/0.77  thf('69', plain,
% 0.57/0.77      (((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.57/0.77         <= (((r1_tarski @ sk_C_1 @ sk_B)) & ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('simplify', [status(thm)], ['68'])).
% 0.57/0.77  thf('70', plain,
% 0.57/0.77      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 0.57/0.77         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.57/0.77             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.57/0.77             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['46', '69'])).
% 0.57/0.77  thf('71', plain,
% 0.57/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X4 @ X5)
% 0.57/0.77          | ~ (r1_tarski @ X5 @ X6)
% 0.57/0.77          | (r1_tarski @ X4 @ X6))),
% 0.57/0.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.57/0.77  thf('72', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ k1_xboole_0 @ X0)))
% 0.57/0.77         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.57/0.77             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.57/0.77             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['70', '71'])).
% 0.57/0.77  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.57/0.77  thf('73', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.57/0.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.57/0.77  thf('74', plain,
% 0.57/0.77      ((![X0 : $i]: (r1_tarski @ sk_C_1 @ X0))
% 0.57/0.77         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.57/0.77             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.57/0.77             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('demod', [status(thm)], ['72', '73'])).
% 0.57/0.77  thf(t49_mcart_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( ~( ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) & 
% 0.57/0.77            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) ) ) & 
% 0.57/0.77            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) ) ) ) =>
% 0.57/0.77       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.57/0.77  thf('75', plain,
% 0.57/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.77         (((X13) = (k1_xboole_0))
% 0.57/0.77          | ~ (r1_tarski @ X13 @ (k3_zfmisc_1 @ X13 @ X14 @ X15)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t49_mcart_1])).
% 0.57/0.77  thf('76', plain,
% 0.57/0.77      ((((sk_C_1) = (k1_xboole_0)))
% 0.57/0.77         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.57/0.77             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.57/0.77             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['74', '75'])).
% 0.57/0.77  thf('77', plain,
% 0.57/0.77      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.57/0.77      inference('split', [status(esa)], ['0'])).
% 0.57/0.77  thf('78', plain,
% 0.57/0.77      ((((sk_C_1) != (sk_C_1)))
% 0.57/0.77         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 0.57/0.77             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.57/0.77             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.57/0.77             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['76', '77'])).
% 0.57/0.77  thf('79', plain,
% 0.57/0.77      (~ ((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.57/0.77       ~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | (((sk_C_1) = (k1_xboole_0)))),
% 0.57/0.77      inference('simplify', [status(thm)], ['78'])).
% 0.57/0.77  thf('80', plain, ($false),
% 0.57/0.77      inference('sat_resolution*', [status(thm)],
% 0.57/0.77                ['1', '3', '5', '38', '39', '79'])).
% 0.57/0.77  
% 0.57/0.77  % SZS output end Refutation
% 0.57/0.77  
% 0.57/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
