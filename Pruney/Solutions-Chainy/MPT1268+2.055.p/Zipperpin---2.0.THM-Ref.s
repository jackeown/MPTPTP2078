%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DdrezdmVya

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:24 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 180 expanded)
%              Number of leaves         :   27 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  908 (2426 expanded)
%              Number of equality atoms :   40 (  97 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X22 @ sk_A )
      | ~ ( r1_tarski @ X22 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B_1 ) )
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X3 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B_1 ) )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('22',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('26',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['22','23','29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X21 @ X20 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('39',plain,
    ( ~ ! [X22: $i] :
          ( ( X22 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X22 @ sk_A )
          | ~ ( r1_tarski @ X22 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tops_1 @ X20 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X20 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('50',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('51',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('52',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,
    ( ( ( k2_xboole_0 @ sk_C @ sk_B_1 )
      = sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X3 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X16 )
      | ~ ( v3_pre_topc @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r2_hidden @ X18 @ ( k1_tops_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( r1_tarski @ sk_C @ sk_B_1 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( v3_pre_topc @ sk_C @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','68'])).

thf('70',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','69'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('72',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ sk_C ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','72'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('74',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','39','41','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DdrezdmVya
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.86  % Solved by: fo/fo7.sh
% 0.67/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.86  % done 939 iterations in 0.410s
% 0.67/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.86  % SZS output start Refutation
% 0.67/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.86  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.67/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.86  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.67/0.86  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.67/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.86  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.67/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.86  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.67/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.86  thf(t86_tops_1, conjecture,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86           ( ( v2_tops_1 @ B @ A ) <=>
% 0.67/0.86             ( ![C:$i]:
% 0.67/0.86               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.67/0.86                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.67/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.86    (~( ![A:$i]:
% 0.67/0.86        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.86          ( ![B:$i]:
% 0.67/0.86            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86              ( ( v2_tops_1 @ B @ A ) <=>
% 0.67/0.86                ( ![C:$i]:
% 0.67/0.86                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.67/0.86                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.67/0.86    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.67/0.86  thf('0', plain,
% 0.67/0.86      ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('1', plain,
% 0.67/0.86      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.86      inference('split', [status(esa)], ['0'])).
% 0.67/0.86  thf('2', plain,
% 0.67/0.86      (((r1_tarski @ sk_C @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('3', plain,
% 0.67/0.86      (((r1_tarski @ sk_C @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.86      inference('split', [status(esa)], ['2'])).
% 0.67/0.86  thf('4', plain,
% 0.67/0.86      (![X22 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.86          | ((X22) = (k1_xboole_0))
% 0.67/0.86          | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.86          | ~ (r1_tarski @ X22 @ sk_B_1)
% 0.67/0.86          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('5', plain,
% 0.67/0.86      ((![X22 : $i]:
% 0.67/0.86          (((X22) = (k1_xboole_0))
% 0.67/0.86           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.86           | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.86           | ~ (r1_tarski @ X22 @ sk_B_1))) | 
% 0.67/0.86       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.86      inference('split', [status(esa)], ['4'])).
% 0.67/0.86  thf('6', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(t3_subset, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.86  thf('7', plain,
% 0.67/0.86      (![X7 : $i, X8 : $i]:
% 0.67/0.86         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('8', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.67/0.86  thf('9', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(t44_tops_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.67/0.86  thf('10', plain,
% 0.67/0.86      (![X14 : $i, X15 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.67/0.86          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ X14)
% 0.67/0.86          | ~ (l1_pre_topc @ X15))),
% 0.67/0.86      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.67/0.86  thf('11', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.86  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.67/0.86  thf(t12_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.67/0.86  thf('14', plain,
% 0.67/0.86      (![X4 : $i, X5 : $i]:
% 0.67/0.86         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.67/0.86      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.67/0.86  thf('15', plain,
% 0.67/0.86      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1) = (sk_B_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['13', '14'])).
% 0.67/0.86  thf(t11_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.67/0.86  thf('16', plain,
% 0.67/0.86      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.86         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X3) @ X2))),
% 0.67/0.86      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.67/0.86  thf('17', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (r1_tarski @ sk_B_1 @ X0)
% 0.67/0.86          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['15', '16'])).
% 0.67/0.86  thf('18', plain,
% 0.67/0.86      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['8', '17'])).
% 0.67/0.86  thf('19', plain,
% 0.67/0.86      (![X7 : $i, X9 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('20', plain,
% 0.67/0.86      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.86  thf('21', plain,
% 0.67/0.86      ((![X22 : $i]:
% 0.67/0.86          (((X22) = (k1_xboole_0))
% 0.67/0.86           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.86           | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.86           | ~ (r1_tarski @ X22 @ sk_B_1)))
% 0.67/0.86         <= ((![X22 : $i]:
% 0.67/0.86                (((X22) = (k1_xboole_0))
% 0.67/0.86                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.86                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.86                 | ~ (r1_tarski @ X22 @ sk_B_1))))),
% 0.67/0.86      inference('split', [status(esa)], ['4'])).
% 0.67/0.86  thf('22', plain,
% 0.67/0.86      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.67/0.86         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.67/0.86         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.67/0.86         <= ((![X22 : $i]:
% 0.67/0.86                (((X22) = (k1_xboole_0))
% 0.67/0.86                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.86                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.86                 | ~ (r1_tarski @ X22 @ sk_B_1))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['20', '21'])).
% 0.67/0.86  thf('23', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.67/0.86  thf('24', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(fc9_tops_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.67/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.86       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.67/0.86  thf('25', plain,
% 0.67/0.86      (![X12 : $i, X13 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X12)
% 0.67/0.86          | ~ (v2_pre_topc @ X12)
% 0.67/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.67/0.86          | (v3_pre_topc @ (k1_tops_1 @ X12 @ X13) @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.67/0.86  thf('26', plain,
% 0.67/0.86      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.67/0.86        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['24', '25'])).
% 0.67/0.86  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('29', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.67/0.86      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.67/0.86  thf('30', plain,
% 0.67/0.86      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.67/0.86         <= ((![X22 : $i]:
% 0.67/0.86                (((X22) = (k1_xboole_0))
% 0.67/0.86                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.86                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.86                 | ~ (r1_tarski @ X22 @ sk_B_1))))),
% 0.67/0.86      inference('demod', [status(thm)], ['22', '23', '29'])).
% 0.67/0.86  thf('31', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(t84_tops_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86           ( ( v2_tops_1 @ B @ A ) <=>
% 0.67/0.86             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.67/0.86  thf('32', plain,
% 0.67/0.86      (![X20 : $i, X21 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.67/0.87          | ((k1_tops_1 @ X21 @ X20) != (k1_xboole_0))
% 0.67/0.87          | (v2_tops_1 @ X20 @ X21)
% 0.67/0.87          | ~ (l1_pre_topc @ X21))),
% 0.67/0.87      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.67/0.87  thf('33', plain,
% 0.67/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.87        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.67/0.87        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['31', '32'])).
% 0.67/0.87  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('35', plain,
% 0.67/0.87      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.67/0.87        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.67/0.87      inference('demod', [status(thm)], ['33', '34'])).
% 0.67/0.87  thf('36', plain,
% 0.67/0.87      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.67/0.87         <= ((![X22 : $i]:
% 0.67/0.87                (((X22) = (k1_xboole_0))
% 0.67/0.87                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.87                 | ~ (r1_tarski @ X22 @ sk_B_1))))),
% 0.67/0.87      inference('sup-', [status(thm)], ['30', '35'])).
% 0.67/0.87  thf('37', plain,
% 0.67/0.87      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.67/0.87         <= ((![X22 : $i]:
% 0.67/0.87                (((X22) = (k1_xboole_0))
% 0.67/0.87                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.87                 | ~ (r1_tarski @ X22 @ sk_B_1))))),
% 0.67/0.87      inference('simplify', [status(thm)], ['36'])).
% 0.67/0.87  thf('38', plain,
% 0.67/0.87      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.67/0.87      inference('split', [status(esa)], ['2'])).
% 0.67/0.87  thf('39', plain,
% 0.67/0.87      (~
% 0.67/0.87       (![X22 : $i]:
% 0.67/0.87          (((X22) = (k1_xboole_0))
% 0.67/0.87           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87           | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.67/0.87           | ~ (r1_tarski @ X22 @ sk_B_1))) | 
% 0.67/0.87       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.87  thf('40', plain,
% 0.67/0.87      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('41', plain,
% 0.67/0.87      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.87      inference('split', [status(esa)], ['40'])).
% 0.67/0.87  thf('42', plain,
% 0.67/0.87      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.67/0.87      inference('split', [status(esa)], ['4'])).
% 0.67/0.87  thf('43', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('44', plain,
% 0.67/0.87      (![X20 : $i, X21 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.67/0.87          | ~ (v2_tops_1 @ X20 @ X21)
% 0.67/0.87          | ((k1_tops_1 @ X21 @ X20) = (k1_xboole_0))
% 0.67/0.87          | ~ (l1_pre_topc @ X21))),
% 0.67/0.87      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.67/0.87  thf('45', plain,
% 0.67/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.87        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.67/0.87        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.87  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('47', plain,
% 0.67/0.87      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.67/0.87        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.67/0.87      inference('demod', [status(thm)], ['45', '46'])).
% 0.67/0.87  thf('48', plain,
% 0.67/0.87      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.67/0.87         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['42', '47'])).
% 0.67/0.87  thf(t7_xboole_0, axiom,
% 0.67/0.87    (![A:$i]:
% 0.67/0.87     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.67/0.87          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.67/0.87  thf('49', plain,
% 0.67/0.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.67/0.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.67/0.87  thf('50', plain,
% 0.67/0.87      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.67/0.87      inference('split', [status(esa)], ['40'])).
% 0.67/0.87  thf('51', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['6', '7'])).
% 0.67/0.87  thf('52', plain,
% 0.67/0.87      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.67/0.87      inference('split', [status(esa)], ['2'])).
% 0.67/0.87  thf('53', plain,
% 0.67/0.87      (![X4 : $i, X5 : $i]:
% 0.67/0.87         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.67/0.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.67/0.87  thf('54', plain,
% 0.67/0.87      ((((k2_xboole_0 @ sk_C @ sk_B_1) = (sk_B_1)))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['52', '53'])).
% 0.67/0.87  thf('55', plain,
% 0.67/0.87      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.87         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X3) @ X2))),
% 0.67/0.87      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.67/0.87  thf('56', plain,
% 0.67/0.87      ((![X0 : $i]: (~ (r1_tarski @ sk_B_1 @ X0) | (r1_tarski @ sk_C @ X0)))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.87  thf('57', plain,
% 0.67/0.87      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['51', '56'])).
% 0.67/0.87  thf('58', plain,
% 0.67/0.87      (![X7 : $i, X9 : $i]:
% 0.67/0.87         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.67/0.87      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.87  thf('59', plain,
% 0.67/0.87      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['57', '58'])).
% 0.67/0.87  thf('60', plain,
% 0.67/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(t54_tops_1, axiom,
% 0.67/0.87    (![A:$i]:
% 0.67/0.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.87       ( ![B:$i,C:$i]:
% 0.67/0.87         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.87           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.67/0.87             ( ?[D:$i]:
% 0.67/0.87               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.67/0.87                 ( v3_pre_topc @ D @ A ) & 
% 0.67/0.87                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.67/0.87  thf('61', plain,
% 0.67/0.87      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.87         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.67/0.87          | ~ (r2_hidden @ X18 @ X19)
% 0.67/0.87          | ~ (r1_tarski @ X19 @ X16)
% 0.67/0.87          | ~ (v3_pre_topc @ X19 @ X17)
% 0.67/0.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.67/0.87          | (r2_hidden @ X18 @ (k1_tops_1 @ X17 @ X16))
% 0.67/0.87          | ~ (l1_pre_topc @ X17)
% 0.67/0.87          | ~ (v2_pre_topc @ X17))),
% 0.67/0.87      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.67/0.87  thf('62', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (~ (v2_pre_topc @ sk_A)
% 0.67/0.87          | ~ (l1_pre_topc @ sk_A)
% 0.67/0.87          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.67/0.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.67/0.87          | ~ (r1_tarski @ X1 @ sk_B_1)
% 0.67/0.87          | ~ (r2_hidden @ X0 @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['60', '61'])).
% 0.67/0.87  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('65', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.67/0.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.87          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.67/0.87          | ~ (r1_tarski @ X1 @ sk_B_1)
% 0.67/0.87          | ~ (r2_hidden @ X0 @ X1))),
% 0.67/0.87      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.67/0.87  thf('66', plain,
% 0.67/0.87      ((![X0 : $i]:
% 0.67/0.87          (~ (r2_hidden @ X0 @ sk_C)
% 0.67/0.87           | ~ (r1_tarski @ sk_C @ sk_B_1)
% 0.67/0.87           | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.67/0.87           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['59', '65'])).
% 0.67/0.87  thf('67', plain,
% 0.67/0.87      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.67/0.87      inference('split', [status(esa)], ['2'])).
% 0.67/0.87  thf('68', plain,
% 0.67/0.87      ((![X0 : $i]:
% 0.67/0.87          (~ (r2_hidden @ X0 @ sk_C)
% 0.67/0.87           | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.67/0.87           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.67/0.87      inference('demod', [status(thm)], ['66', '67'])).
% 0.67/0.87  thf('69', plain,
% 0.67/0.87      ((![X0 : $i]:
% 0.67/0.87          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.67/0.87           | ~ (r2_hidden @ X0 @ sk_C)))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['50', '68'])).
% 0.67/0.87  thf('70', plain,
% 0.67/0.87      (((((sk_C) = (k1_xboole_0))
% 0.67/0.87         | (r2_hidden @ (sk_B @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['49', '69'])).
% 0.67/0.87  thf(t7_ordinal1, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.87  thf('71', plain,
% 0.67/0.87      (![X10 : $i, X11 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.67/0.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.67/0.87  thf('72', plain,
% 0.67/0.87      (((((sk_C) = (k1_xboole_0))
% 0.67/0.87         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_C))))
% 0.67/0.87         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['70', '71'])).
% 0.67/0.87  thf('73', plain,
% 0.67/0.87      (((~ (r1_tarski @ k1_xboole_0 @ (sk_B @ sk_C)) | ((sk_C) = (k1_xboole_0))))
% 0.67/0.87         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.67/0.87             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 0.67/0.87             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['48', '72'])).
% 0.67/0.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.67/0.87  thf('74', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.67/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.87  thf('75', plain,
% 0.67/0.87      ((((sk_C) = (k1_xboole_0)))
% 0.67/0.87         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.67/0.87             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 0.67/0.87             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.67/0.87      inference('demod', [status(thm)], ['73', '74'])).
% 0.67/0.87  thf('76', plain,
% 0.67/0.87      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.67/0.87      inference('split', [status(esa)], ['0'])).
% 0.67/0.87  thf('77', plain,
% 0.67/0.87      ((((sk_C) != (sk_C)))
% 0.67/0.87         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.67/0.87             ((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 0.67/0.87             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 0.67/0.87             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['75', '76'])).
% 0.67/0.87  thf('78', plain,
% 0.67/0.87      (~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.67/0.87       ~ ((r1_tarski @ sk_C @ sk_B_1)) | (((sk_C) = (k1_xboole_0)))),
% 0.67/0.87      inference('simplify', [status(thm)], ['77'])).
% 0.67/0.87  thf('79', plain, ($false),
% 0.67/0.87      inference('sat_resolution*', [status(thm)],
% 0.67/0.87                ['1', '3', '5', '39', '41', '78'])).
% 0.67/0.87  
% 0.67/0.87  % SZS output end Refutation
% 0.67/0.87  
% 0.67/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
