%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5vSlNPrdJN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:17 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 726 expanded)
%              Number of leaves         :   31 ( 201 expanded)
%              Depth                    :   22
%              Number of atoms          : 1140 (10781 expanded)
%              Number of equality atoms :   62 ( 458 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('1',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X39: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X39 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X39 @ sk_A )
      | ~ ( r1_tarski @ X39 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) )
   <= ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X25 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('28',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','31'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k1_tops_1 @ X38 @ X37 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ! [X39: $i] :
          ( ( X39 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X39 @ sk_A )
          | ~ ( r1_tarski @ X39 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('44',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) )
   <= ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('51',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ sk_B )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( ! [X39: $i] :
          ( ( X39 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X39 @ sk_A )
          | ~ ( r1_tarski @ X39 @ sk_B ) )
      & ( r1_tarski @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('53',plain,
    ( ( ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( ! [X39: $i] :
          ( ( X39 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X39 @ sk_A )
          | ~ ( r1_tarski @ X39 @ sk_B ) )
      & ( r1_tarski @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ! [X39: $i] :
          ( ( X39 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X39 @ sk_A )
          | ~ ( r1_tarski @ X39 @ sk_B ) )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf('55',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('56',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ! [X39: $i] :
          ( ( X39 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X39 @ sk_A )
          | ~ ( r1_tarski @ X39 @ sk_B ) )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ! [X39: $i] :
          ( ( X39 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X39 @ sk_A )
          | ~ ( r1_tarski @ X39 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X39: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X39 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X39 @ sk_A )
      | ~ ( r1_tarski @ X39 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X39: $i] :
        ( ( X39 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X39 @ sk_A )
        | ~ ( r1_tarski @ X39 @ sk_B ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','6','8','41','57','59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['2','61'])).

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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r1_tarski @ X32 @ X29 )
      | ~ ( v3_pre_topc @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r2_hidden @ X31 @ ( k1_tops_1 @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
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
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tops_1 @ X37 @ X38 )
      | ( ( k1_tops_1 @ X38 @ X37 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','6','8','41','57','59'])).

thf('77',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ sk_B )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('81',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['6','8','41','57','59','4'])).

thf('82',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('84',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','8','41','57','59','6'])).

thf('85',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','86'])).

thf('88',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ sk_C_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('92',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('94',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('97',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('98',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','98'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('100',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','101'])).

thf('103',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('104',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','6','41','57','59','8'])).

thf('105',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5vSlNPrdJN
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:39:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.51/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.72  % Solved by: fo/fo7.sh
% 0.51/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.72  % done 991 iterations in 0.285s
% 0.51/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.72  % SZS output start Refutation
% 0.51/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.72  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.51/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.72  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.51/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.72  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.51/0.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.51/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.72  thf(d3_tarski, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.72  thf('0', plain,
% 0.51/0.72      (![X3 : $i, X5 : $i]:
% 0.51/0.72         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.51/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.72  thf(t86_tops_1, conjecture,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72           ( ( v2_tops_1 @ B @ A ) <=>
% 0.51/0.72             ( ![C:$i]:
% 0.51/0.72               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.51/0.72                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.72    (~( ![A:$i]:
% 0.51/0.72        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72          ( ![B:$i]:
% 0.51/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72              ( ( v2_tops_1 @ B @ A ) <=>
% 0.51/0.72                ( ![C:$i]:
% 0.51/0.72                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.51/0.72                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.51/0.72    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.51/0.72  thf('1', plain,
% 0.51/0.72      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('2', plain,
% 0.51/0.72      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.51/0.72         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.51/0.72      inference('split', [status(esa)], ['1'])).
% 0.51/0.72  thf('3', plain,
% 0.51/0.72      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('4', plain,
% 0.51/0.72      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('split', [status(esa)], ['3'])).
% 0.51/0.72  thf('5', plain,
% 0.51/0.72      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('6', plain,
% 0.51/0.72      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('split', [status(esa)], ['5'])).
% 0.51/0.72  thf('7', plain,
% 0.51/0.72      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('8', plain,
% 0.51/0.72      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('split', [status(esa)], ['7'])).
% 0.51/0.72  thf('9', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t3_subset, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.72  thf('10', plain,
% 0.51/0.72      (![X20 : $i, X21 : $i]:
% 0.51/0.72         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.72  thf('11', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.72  thf('12', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t44_tops_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( l1_pre_topc @ A ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.51/0.72  thf('13', plain,
% 0.51/0.72      (![X27 : $i, X28 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.51/0.72          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ X27)
% 0.51/0.72          | ~ (l1_pre_topc @ X28))),
% 0.51/0.72      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.51/0.72  thf('14', plain,
% 0.51/0.72      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.51/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.72  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('16', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.51/0.72      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.72  thf(t1_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.51/0.72       ( r1_tarski @ A @ C ) ))).
% 0.51/0.72  thf('17', plain,
% 0.51/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.51/0.72         (~ (r1_tarski @ X8 @ X9)
% 0.51/0.72          | ~ (r1_tarski @ X9 @ X10)
% 0.51/0.72          | (r1_tarski @ X8 @ X10))),
% 0.51/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.51/0.72  thf('18', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.51/0.72          | ~ (r1_tarski @ sk_B @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.72  thf('19', plain,
% 0.51/0.72      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['11', '18'])).
% 0.51/0.72  thf('20', plain,
% 0.51/0.72      (![X20 : $i, X22 : $i]:
% 0.51/0.72         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.51/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.72  thf('21', plain,
% 0.51/0.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.51/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.72  thf('22', plain,
% 0.51/0.72      (![X39 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72          | ((X39) = (k1_xboole_0))
% 0.51/0.72          | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72          | ~ (r1_tarski @ X39 @ sk_B)
% 0.51/0.72          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('23', plain,
% 0.51/0.72      ((![X39 : $i]:
% 0.51/0.72          (((X39) = (k1_xboole_0))
% 0.51/0.72           | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72           | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72           | ~ (r1_tarski @ X39 @ sk_B)))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))))),
% 0.51/0.72      inference('split', [status(esa)], ['22'])).
% 0.51/0.72  thf('24', plain,
% 0.51/0.72      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.51/0.72         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.51/0.72         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['21', '23'])).
% 0.51/0.72  thf('25', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.51/0.72      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.72  thf('26', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(fc9_tops_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.51/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.72       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.51/0.72  thf('27', plain,
% 0.51/0.72      (![X25 : $i, X26 : $i]:
% 0.51/0.72         (~ (l1_pre_topc @ X25)
% 0.51/0.72          | ~ (v2_pre_topc @ X25)
% 0.51/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.51/0.72          | (v3_pre_topc @ (k1_tops_1 @ X25 @ X26) @ X25))),
% 0.51/0.72      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.51/0.72  thf('28', plain,
% 0.51/0.72      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.51/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.51/0.72  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('31', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.51/0.72      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.51/0.72  thf('32', plain,
% 0.51/0.72      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))))),
% 0.51/0.72      inference('demod', [status(thm)], ['24', '25', '31'])).
% 0.51/0.72  thf('33', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t84_tops_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( l1_pre_topc @ A ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72           ( ( v2_tops_1 @ B @ A ) <=>
% 0.51/0.72             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.51/0.72  thf('34', plain,
% 0.51/0.72      (![X37 : $i, X38 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.51/0.72          | ((k1_tops_1 @ X38 @ X37) != (k1_xboole_0))
% 0.51/0.72          | (v2_tops_1 @ X37 @ X38)
% 0.51/0.72          | ~ (l1_pre_topc @ X38))),
% 0.51/0.72      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.51/0.72  thf('35', plain,
% 0.51/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.51/0.72        | (v2_tops_1 @ sk_B @ sk_A)
% 0.51/0.72        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.72  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('37', plain,
% 0.51/0.72      (((v2_tops_1 @ sk_B @ sk_A)
% 0.51/0.72        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.51/0.72      inference('demod', [status(thm)], ['35', '36'])).
% 0.51/0.72  thf('38', plain,
% 0.51/0.72      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['32', '37'])).
% 0.51/0.72  thf('39', plain,
% 0.51/0.72      (((v2_tops_1 @ sk_B @ sk_A))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))))),
% 0.51/0.72      inference('simplify', [status(thm)], ['38'])).
% 0.51/0.72  thf('40', plain,
% 0.51/0.72      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['3'])).
% 0.51/0.72  thf('41', plain,
% 0.51/0.72      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.51/0.72       ~
% 0.51/0.72       (![X39 : $i]:
% 0.51/0.72          (((X39) = (k1_xboole_0))
% 0.51/0.72           | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72           | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72           | ~ (r1_tarski @ X39 @ sk_B)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.51/0.72  thf('42', plain,
% 0.51/0.72      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['5'])).
% 0.51/0.72  thf('43', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.72  thf('44', plain,
% 0.51/0.72      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.51/0.72      inference('split', [status(esa)], ['3'])).
% 0.51/0.72  thf('45', plain,
% 0.51/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.51/0.72         (~ (r1_tarski @ X8 @ X9)
% 0.51/0.72          | ~ (r1_tarski @ X9 @ X10)
% 0.51/0.72          | (r1_tarski @ X8 @ X10))),
% 0.51/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.51/0.72  thf('46', plain,
% 0.51/0.72      ((![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.51/0.72         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.51/0.72  thf('47', plain,
% 0.51/0.72      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['43', '46'])).
% 0.51/0.72  thf('48', plain,
% 0.51/0.72      (![X20 : $i, X22 : $i]:
% 0.51/0.72         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.51/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.72  thf('49', plain,
% 0.51/0.72      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.51/0.72         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['47', '48'])).
% 0.51/0.72  thf('50', plain,
% 0.51/0.72      ((![X39 : $i]:
% 0.51/0.72          (((X39) = (k1_xboole_0))
% 0.51/0.72           | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72           | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72           | ~ (r1_tarski @ X39 @ sk_B)))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))))),
% 0.51/0.72      inference('split', [status(esa)], ['22'])).
% 0.51/0.72  thf('51', plain,
% 0.51/0.72      (((~ (r1_tarski @ sk_C_1 @ sk_B)
% 0.51/0.72         | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.51/0.72         | ((sk_C_1) = (k1_xboole_0))))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))) & 
% 0.51/0.72             ((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['49', '50'])).
% 0.51/0.72  thf('52', plain,
% 0.51/0.72      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.51/0.72      inference('split', [status(esa)], ['3'])).
% 0.51/0.72  thf('53', plain,
% 0.51/0.72      (((~ (v3_pre_topc @ sk_C_1 @ sk_A) | ((sk_C_1) = (k1_xboole_0))))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))) & 
% 0.51/0.72             ((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.51/0.72      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.72  thf('54', plain,
% 0.51/0.72      ((((sk_C_1) = (k1_xboole_0)))
% 0.51/0.72         <= ((![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))) & 
% 0.51/0.72             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.51/0.72             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['42', '53'])).
% 0.51/0.72  thf('55', plain,
% 0.51/0.72      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.51/0.72      inference('split', [status(esa)], ['7'])).
% 0.51/0.72  thf('56', plain,
% 0.51/0.72      ((((sk_C_1) != (sk_C_1)))
% 0.51/0.72         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 0.51/0.72             (![X39 : $i]:
% 0.51/0.72                (((X39) = (k1_xboole_0))
% 0.51/0.72                 | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72                 | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72                 | ~ (r1_tarski @ X39 @ sk_B))) & 
% 0.51/0.72             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.51/0.72             ((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['54', '55'])).
% 0.51/0.72  thf('57', plain,
% 0.51/0.72      (~
% 0.51/0.72       (![X39 : $i]:
% 0.51/0.72          (((X39) = (k1_xboole_0))
% 0.51/0.72           | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72           | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72           | ~ (r1_tarski @ X39 @ sk_B))) | 
% 0.51/0.72       ~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | (((sk_C_1) = (k1_xboole_0))) | 
% 0.51/0.72       ~ ((r1_tarski @ sk_C_1 @ sk_B))),
% 0.51/0.72      inference('simplify', [status(thm)], ['56'])).
% 0.51/0.72  thf('58', plain,
% 0.51/0.72      (![X39 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72          | ((X39) = (k1_xboole_0))
% 0.51/0.72          | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72          | ~ (r1_tarski @ X39 @ sk_B)
% 0.51/0.72          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('59', plain,
% 0.51/0.72      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.51/0.72       (![X39 : $i]:
% 0.51/0.72          (((X39) = (k1_xboole_0))
% 0.51/0.72           | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72           | ~ (v3_pre_topc @ X39 @ sk_A)
% 0.51/0.72           | ~ (r1_tarski @ X39 @ sk_B)))),
% 0.51/0.72      inference('split', [status(esa)], ['58'])).
% 0.51/0.72  thf('60', plain,
% 0.51/0.72      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.51/0.72       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('split', [status(esa)], ['1'])).
% 0.51/0.72  thf('61', plain,
% 0.51/0.72      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.72      inference('sat_resolution*', [status(thm)],
% 0.51/0.72                ['4', '6', '8', '41', '57', '59', '60'])).
% 0.51/0.72  thf('62', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['2', '61'])).
% 0.51/0.72  thf('63', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t54_tops_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i,C:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.51/0.72             ( ?[D:$i]:
% 0.51/0.72               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.51/0.72                 ( v3_pre_topc @ D @ A ) & 
% 0.51/0.72                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('64', plain,
% 0.51/0.72      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.51/0.72          | ~ (r2_hidden @ X31 @ X32)
% 0.51/0.72          | ~ (r1_tarski @ X32 @ X29)
% 0.51/0.72          | ~ (v3_pre_topc @ X32 @ X30)
% 0.51/0.72          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.51/0.72          | (r2_hidden @ X31 @ (k1_tops_1 @ X30 @ X29))
% 0.51/0.72          | ~ (l1_pre_topc @ X30)
% 0.51/0.72          | ~ (v2_pre_topc @ X30))),
% 0.51/0.72      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.51/0.72  thf('65', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (v2_pre_topc @ sk_A)
% 0.51/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.51/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.51/0.72          | ~ (r1_tarski @ X1 @ sk_B)
% 0.51/0.72          | ~ (r2_hidden @ X0 @ X1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['63', '64'])).
% 0.51/0.72  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('68', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.51/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.51/0.72          | ~ (r1_tarski @ X1 @ sk_B)
% 0.51/0.72          | ~ (r2_hidden @ X0 @ X1))),
% 0.51/0.72      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.51/0.72  thf('69', plain,
% 0.51/0.72      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['58'])).
% 0.51/0.72  thf('70', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('71', plain,
% 0.51/0.72      (![X37 : $i, X38 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.51/0.72          | ~ (v2_tops_1 @ X37 @ X38)
% 0.51/0.72          | ((k1_tops_1 @ X38 @ X37) = (k1_xboole_0))
% 0.51/0.72          | ~ (l1_pre_topc @ X38))),
% 0.51/0.72      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.51/0.72  thf('72', plain,
% 0.51/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.51/0.72        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.51/0.72        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['70', '71'])).
% 0.51/0.72  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('74', plain,
% 0.51/0.72      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.51/0.72        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('demod', [status(thm)], ['72', '73'])).
% 0.51/0.72  thf('75', plain,
% 0.51/0.72      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.51/0.72         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['69', '74'])).
% 0.51/0.72  thf('76', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.51/0.72      inference('sat_resolution*', [status(thm)],
% 0.51/0.72                ['4', '6', '8', '41', '57', '59'])).
% 0.51/0.72  thf('77', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.51/0.72  thf('78', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.51/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.72          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.51/0.72          | ~ (r1_tarski @ X1 @ sk_B)
% 0.51/0.72          | ~ (r2_hidden @ X0 @ X1))),
% 0.51/0.72      inference('demod', [status(thm)], ['68', '77'])).
% 0.51/0.72  thf('79', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.51/0.72          | ~ (r1_tarski @ sk_C_1 @ sk_B)
% 0.51/0.72          | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.51/0.72          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['62', '78'])).
% 0.51/0.72  thf('80', plain,
% 0.51/0.72      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.51/0.72      inference('split', [status(esa)], ['3'])).
% 0.51/0.72  thf('81', plain, (((r1_tarski @ sk_C_1 @ sk_B))),
% 0.51/0.72      inference('sat_resolution*', [status(thm)],
% 0.51/0.72                ['6', '8', '41', '57', '59', '4'])).
% 0.51/0.72  thf('82', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.51/0.72  thf('83', plain,
% 0.51/0.72      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('split', [status(esa)], ['5'])).
% 0.51/0.72  thf('84', plain, (((v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.51/0.72      inference('sat_resolution*', [status(thm)],
% 0.51/0.72                ['4', '8', '41', '57', '59', '6'])).
% 0.51/0.72  thf('85', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.51/0.72  thf('86', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X0 @ sk_C_1) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.51/0.72      inference('demod', [status(thm)], ['79', '82', '85'])).
% 0.51/0.72  thf('87', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_tarski @ sk_C_1 @ X0)
% 0.51/0.72          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ k1_xboole_0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['0', '86'])).
% 0.51/0.72  thf('88', plain,
% 0.51/0.72      (![X3 : $i, X5 : $i]:
% 0.51/0.72         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.51/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.72  thf('89', plain,
% 0.51/0.72      (((r1_tarski @ sk_C_1 @ k1_xboole_0) | (r1_tarski @ sk_C_1 @ k1_xboole_0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['87', '88'])).
% 0.51/0.72  thf('90', plain, ((r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.51/0.72      inference('simplify', [status(thm)], ['89'])).
% 0.51/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.72  thf('91', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.72  thf(t2_boole, axiom,
% 0.51/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.51/0.72  thf('92', plain,
% 0.51/0.72      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.72  thf('93', plain,
% 0.51/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.51/0.72      inference('sup+', [status(thm)], ['91', '92'])).
% 0.51/0.72  thf(t100_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.72  thf('94', plain,
% 0.51/0.72      (![X6 : $i, X7 : $i]:
% 0.51/0.72         ((k4_xboole_0 @ X6 @ X7)
% 0.51/0.72           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.72  thf('95', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.72           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.51/0.72      inference('sup+', [status(thm)], ['93', '94'])).
% 0.51/0.72  thf('96', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.72           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.51/0.72      inference('sup+', [status(thm)], ['93', '94'])).
% 0.51/0.72  thf(t3_boole, axiom,
% 0.51/0.72    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.72  thf('97', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.51/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.72  thf('98', plain,
% 0.51/0.72      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.72      inference('sup+', [status(thm)], ['96', '97'])).
% 0.51/0.72  thf('99', plain,
% 0.51/0.72      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.51/0.72      inference('demod', [status(thm)], ['95', '98'])).
% 0.51/0.72  thf(t38_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.51/0.72       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.51/0.72  thf('100', plain,
% 0.51/0.72      (![X13 : $i, X14 : $i]:
% 0.51/0.72         (((X13) = (k1_xboole_0))
% 0.51/0.72          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.51/0.72  thf('101', plain,
% 0.51/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['99', '100'])).
% 0.51/0.72  thf('102', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['90', '101'])).
% 0.51/0.72  thf('103', plain,
% 0.51/0.72      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.51/0.72      inference('split', [status(esa)], ['7'])).
% 0.51/0.72  thf('104', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.51/0.72      inference('sat_resolution*', [status(thm)],
% 0.51/0.72                ['4', '6', '41', '57', '59', '8'])).
% 0.51/0.72  thf('105', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['103', '104'])).
% 0.51/0.72  thf('106', plain, ($false),
% 0.51/0.72      inference('simplify_reflect-', [status(thm)], ['102', '105'])).
% 0.51/0.72  
% 0.51/0.72  % SZS output end Refutation
% 0.51/0.72  
% 0.51/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
