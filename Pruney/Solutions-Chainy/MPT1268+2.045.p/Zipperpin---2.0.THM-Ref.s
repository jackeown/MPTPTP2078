%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HmZaFW1EXK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 (1714 expanded)
%              Number of leaves         :   26 ( 444 expanded)
%              Depth                    :   22
%              Number of atoms          : 1501 (27793 expanded)
%              Number of equality atoms :   73 (1162 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X29 @ sk_A )
      | ~ ( r1_tarski @ X29 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('32',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k1_tops_1 @ X28 @ X27 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('45',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ! [X29: $i] :
          ( ( X29 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X29 @ sk_A )
          | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('47',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('49',plain,
    ( ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('50',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_B )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ! [X29: $i] :
          ( ( X29 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X29 @ sk_A )
          | ~ ( r1_tarski @ X29 @ sk_B ) )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( ! [X29: $i] :
          ( ( X29 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X29 @ sk_A )
          | ~ ( r1_tarski @ X29 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ! [X29: $i] :
          ( ( X29 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X29 @ sk_A )
          | ~ ( r1_tarski @ X29 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('54',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ! [X29: $i] :
          ( ( X29 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X29 @ sk_A )
          | ~ ( r1_tarski @ X29 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ! [X29: $i] :
          ( ( X29 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X29 @ sk_A )
          | ~ ( r1_tarski @ X29 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X29 @ sk_A )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['8','10','12','45','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['6','58'])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X24 )
        = X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('63',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( l1_pre_topc @ X23 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( v3_pre_topc @ X24 @ X23 )
        | ( ( k1_tops_1 @ X23 @ X24 )
          = X24 ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( l1_pre_topc @ X23 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( v3_pre_topc @ X24 @ X23 )
        | ( ( k1_tops_1 @ X23 @ X24 )
          = X24 ) ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X24 )
        = X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('66',plain,
    ( ! [X25: $i,X26: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
        | ~ ( l1_pre_topc @ X26 )
        | ~ ( v2_pre_topc @ X26 ) )
   <= ! [X25: $i,X26: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
        | ~ ( l1_pre_topc @ X26 )
        | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X25: $i,X26: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
        | ~ ( l1_pre_topc @ X26 )
        | ~ ( v2_pre_topc @ X26 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ! [X25: $i,X26: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
        | ~ ( l1_pre_topc @ X26 )
        | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( l1_pre_topc @ X23 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( v3_pre_topc @ X24 @ X23 )
        | ( ( k1_tops_1 @ X23 @ X24 )
          = X24 ) )
    | ! [X25: $i,X26: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
        | ~ ( l1_pre_topc @ X26 )
        | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(split,[status(esa)],['65'])).

thf('72',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X24 )
        = X24 ) ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X24 )
        = X24 ) ) ),
    inference(simpl_trail,[status(thm)],['63','72'])).

thf('74',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','76'])).

thf('78',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['8','12','57','45','55','56','10'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['8','10','12','45','55','56','57'])).

thf('80',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['59','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('84',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['10','12','57','45','55','56','8'])).

thf('85',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tops_1 @ X27 @ X28 )
      | ( ( k1_tops_1 @ X28 @ X27 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['8','10','12','57','45','55','56'])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['82','85','94'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('96',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('97',plain,
    ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
    = sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('99',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('100',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('101',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_B )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ k1_xboole_0 @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('108',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('112',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X24 )
        = X24 ) ) ),
    inference(simpl_trail,[status(thm)],['63','72'])).

thf('113',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('115',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('116',plain,
    ( ( v3_pre_topc @ k1_xboole_0 @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['113','116','117'])).

thf('119',plain,
    ( ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['110','118'])).

thf('120',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('121',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('122',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('123',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['8','10','12','57','45','55','56'])).

thf('126',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['124','125'])).

thf('127',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['82','85','94'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('128',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    r1_xboole_0 @ sk_C @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['97','132'])).

thf('134',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('135',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['8','10','57','45','55','56','12'])).

thf('136',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['133','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HmZaFW1EXK
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:26:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 385 iterations in 0.100s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.57  thf(t86_tops_1, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.57             ( ![C:$i]:
% 0.21/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.57                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57              ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.57                ( ![C:$i]:
% 0.21/0.57                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.57                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['1'])).
% 0.21/0.57  thf(t48_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57               ( ( r1_tarski @ B @ C ) =>
% 0.21/0.57                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.57          | ~ (r1_tarski @ X20 @ X22)
% 0.21/0.57          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ (k1_tops_1 @ X21 @ X22))
% 0.21/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.57          | ~ (l1_pre_topc @ X21))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (l1_pre_topc @ sk_A)
% 0.21/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.57           | ~ (r1_tarski @ sk_C @ X0)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.57  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.57           | ~ (r1_tarski @ sk_C @ X0)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('7', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('11', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t3_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i]:
% 0.21/0.57         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('15', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t44_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('20', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf(t1_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.57       ( r1_tarski @ A @ C ) ))).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.57          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | (r1_tarski @ X3 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.57          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X13 : $i, X15 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X29 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ((X29) = (k1_xboole_0))
% 0.21/0.57          | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57          | ~ (r1_tarski @ X29 @ sk_B)
% 0.21/0.57          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      ((![X29 : $i]:
% 0.21/0.57          (((X29) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X29 @ sk_B)))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 0.21/0.57      inference('split', [status(esa)], ['26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.57         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.57  thf('29', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(fc9_tops_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.57       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X16)
% 0.21/0.57          | ~ (v2_pre_topc @ X16)
% 0.21/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.57          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('35', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['28', '29', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t84_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.57             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X27 : $i, X28 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.57          | ((k1_tops_1 @ X28 @ X27) != (k1_xboole_0))
% 0.21/0.57          | (v2_tops_1 @ X27 @ X28)
% 0.21/0.57          | ~ (l1_pre_topc @ X28))),
% 0.21/0.57      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | (v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['36', '41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['7'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.21/0.57       ~
% 0.21/0.57       (![X29 : $i]:
% 0.21/0.57          (((X29) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X29 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['7'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['1'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      ((![X29 : $i]:
% 0.21/0.57          (((X29) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X29 @ sk_B)))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 0.21/0.57      inference('split', [status(esa)], ['26'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (((~ (r1_tarski @ sk_C @ sk_B)
% 0.21/0.57         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.21/0.57         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (((((sk_C) = (k1_xboole_0)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))) & 
% 0.21/0.57             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['47', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.57         <= ((![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))) & 
% 0.21/0.57             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.57             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '51'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      ((((sk_C) != (sk_C)))
% 0.21/0.57         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.21/0.57             (![X29 : $i]:
% 0.21/0.57                (((X29) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X29 @ sk_B))) & 
% 0.21/0.57             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.57             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (~
% 0.21/0.57       (![X29 : $i]:
% 0.21/0.57          (((X29) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X29 @ sk_B))) | 
% 0.21/0.57       (((sk_C) = (k1_xboole_0))) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.57       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.57       ~ ((r1_tarski @ sk_C @ sk_B))),
% 0.21/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.21/0.57       (![X29 : $i]:
% 0.21/0.57          (((X29) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X29 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X29 @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['26'])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.57       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['1'])).
% 0.21/0.57  thf('58', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['8', '10', '12', '45', '55', '56', '57'])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.57          | ~ (r1_tarski @ sk_C @ X0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['6', '58'])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['1'])).
% 0.21/0.57  thf(t55_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( l1_pre_topc @ B ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57               ( ![D:$i]:
% 0.21/0.57                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.57                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.21/0.57                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.21/0.57                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.21/0.57                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X23)
% 0.21/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | ~ (v3_pre_topc @ X24 @ X23)
% 0.21/0.57          | ((k1_tops_1 @ X23 @ X24) = (X24))
% 0.21/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57          | ~ (l1_pre_topc @ X26)
% 0.21/0.57          | ~ (v2_pre_topc @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      ((![X23 : $i, X24 : $i]:
% 0.21/0.57          (~ (l1_pre_topc @ X23)
% 0.21/0.57           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57           | ~ (v3_pre_topc @ X24 @ X23)
% 0.21/0.57           | ((k1_tops_1 @ X23 @ X24) = (X24))))
% 0.21/0.57         <= ((![X23 : $i, X24 : $i]:
% 0.21/0.57                (~ (l1_pre_topc @ X23)
% 0.21/0.57                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X24 @ X23)
% 0.21/0.57                 | ((k1_tops_1 @ X23 @ X24) = (X24)))))),
% 0.21/0.57      inference('split', [status(esa)], ['62'])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X23)
% 0.21/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | ~ (v3_pre_topc @ X24 @ X23)
% 0.21/0.57          | ((k1_tops_1 @ X23 @ X24) = (X24))
% 0.21/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57          | ~ (l1_pre_topc @ X26)
% 0.21/0.57          | ~ (v2_pre_topc @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      ((![X25 : $i, X26 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57           | ~ (l1_pre_topc @ X26)
% 0.21/0.57           | ~ (v2_pre_topc @ X26)))
% 0.21/0.57         <= ((![X25 : $i, X26 : $i]:
% 0.21/0.57                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57                 | ~ (l1_pre_topc @ X26)
% 0.21/0.57                 | ~ (v2_pre_topc @ X26))))),
% 0.21/0.57      inference('split', [status(esa)], ['65'])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= ((![X25 : $i, X26 : $i]:
% 0.21/0.57                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57                 | ~ (l1_pre_topc @ X26)
% 0.21/0.57                 | ~ (v2_pre_topc @ X26))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['64', '66'])).
% 0.21/0.57  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (~
% 0.21/0.57       (![X25 : $i, X26 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57           | ~ (l1_pre_topc @ X26)
% 0.21/0.57           | ~ (v2_pre_topc @ X26)))),
% 0.21/0.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      ((![X23 : $i, X24 : $i]:
% 0.21/0.57          (~ (l1_pre_topc @ X23)
% 0.21/0.57           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57           | ~ (v3_pre_topc @ X24 @ X23)
% 0.21/0.57           | ((k1_tops_1 @ X23 @ X24) = (X24)))) | 
% 0.21/0.57       (![X25 : $i, X26 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57           | ~ (l1_pre_topc @ X26)
% 0.21/0.57           | ~ (v2_pre_topc @ X26)))),
% 0.21/0.57      inference('split', [status(esa)], ['65'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      ((![X23 : $i, X24 : $i]:
% 0.21/0.57          (~ (l1_pre_topc @ X23)
% 0.21/0.57           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57           | ~ (v3_pre_topc @ X24 @ X23)
% 0.21/0.57           | ((k1_tops_1 @ X23 @ X24) = (X24))))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (![X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X23)
% 0.21/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | ~ (v3_pre_topc @ X24 @ X23)
% 0.21/0.57          | ((k1_tops_1 @ X23 @ X24) = (X24)))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['63', '72'])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.21/0.57         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['61', '73'])).
% 0.21/0.57  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.57  thf('77', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.21/0.57         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['60', '76'])).
% 0.21/0.57  thf('78', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['8', '12', '57', '45', '55', '56', '10'])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['8', '10', '12', '45', '55', '56', '57'])).
% 0.21/0.57  thf('80', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['77', '78', '79'])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.57          | ~ (r1_tarski @ sk_C @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '80'])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.21/0.57        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '81'])).
% 0.21/0.57  thf('83', plain,
% 0.21/0.57      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['7'])).
% 0.21/0.57  thf('84', plain, (((r1_tarski @ sk_C @ sk_B))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['10', '12', '57', '45', '55', '56', '8'])).
% 0.21/0.57  thf('85', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['26'])).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (![X27 : $i, X28 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.57          | ~ (v2_tops_1 @ X27 @ X28)
% 0.21/0.57          | ((k1_tops_1 @ X28 @ X27) = (k1_xboole_0))
% 0.21/0.57          | ~ (l1_pre_topc @ X28))),
% 0.21/0.57      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.57  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('91', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '91'])).
% 0.21/0.57  thf('93', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['8', '10', '12', '57', '45', '55', '56'])).
% 0.21/0.57  thf('94', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.21/0.57  thf('95', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.21/0.57      inference('demod', [status(thm)], ['82', '85', '94'])).
% 0.21/0.57  thf(t28_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('97', plain, (((k3_xboole_0 @ sk_C @ k1_xboole_0) = (sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.57  thf('98', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '91'])).
% 0.21/0.57  thf('100', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      (((r1_tarski @ k1_xboole_0 @ sk_B)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['99', '100'])).
% 0.21/0.57  thf('102', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.57          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | (r1_tarski @ X3 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.57  thf('103', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((r1_tarski @ k1_xboole_0 @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.57  thf('104', plain,
% 0.21/0.57      (((r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['98', '103'])).
% 0.21/0.57  thf('105', plain,
% 0.21/0.57      (![X13 : $i, X15 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('106', plain,
% 0.21/0.57      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.57  thf('108', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | (r1_tarski @ (k1_tops_1 @ sk_A @ k1_xboole_0) @ k1_xboole_0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.57  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('110', plain,
% 0.21/0.57      (((r1_tarski @ (k1_tops_1 @ sk_A @ k1_xboole_0) @ k1_xboole_0))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['108', '109'])).
% 0.21/0.57  thf('111', plain,
% 0.21/0.57      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.57  thf('112', plain,
% 0.21/0.57      (![X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X23)
% 0.21/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | ~ (v3_pre_topc @ X24 @ X23)
% 0.21/0.57          | ((k1_tops_1 @ X23 @ X24) = (X24)))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['63', '72'])).
% 0.21/0.57  thf('113', plain,
% 0.21/0.57      (((((k1_tops_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.57         | ~ (v3_pre_topc @ k1_xboole_0 @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['111', '112'])).
% 0.21/0.57  thf('114', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '91'])).
% 0.21/0.57  thf('115', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.57  thf('116', plain,
% 0.21/0.57      (((v3_pre_topc @ k1_xboole_0 @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['114', '115'])).
% 0.21/0.57  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('118', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['113', '116', '117'])).
% 0.21/0.57  thf('119', plain,
% 0.21/0.57      (((r1_tarski @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['110', '118'])).
% 0.21/0.57  thf('120', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('121', plain,
% 0.21/0.57      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['119', '120'])).
% 0.21/0.57  thf(d7_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.57  thf('122', plain,
% 0.21/0.57      (![X0 : $i, X2 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.57  thf('123', plain,
% 0.21/0.57      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57         | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.57  thf('124', plain,
% 0.21/0.57      (((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['123'])).
% 0.21/0.57  thf('125', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['8', '10', '12', '57', '45', '55', '56'])).
% 0.21/0.57  thf('126', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['124', '125'])).
% 0.21/0.57  thf('127', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.21/0.57      inference('demod', [status(thm)], ['82', '85', '94'])).
% 0.21/0.57  thf(t63_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.57       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.57  thf('128', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X8 @ X9)
% 0.21/0.57          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.21/0.57          | (r1_xboole_0 @ X8 @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.57  thf('129', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_xboole_0 @ sk_C @ X0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['127', '128'])).
% 0.21/0.57  thf('130', plain, ((r1_xboole_0 @ sk_C @ k1_xboole_0)),
% 0.21/0.57      inference('sup-', [status(thm)], ['126', '129'])).
% 0.21/0.57  thf('131', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.57  thf('132', plain, (((k3_xboole_0 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['130', '131'])).
% 0.21/0.57  thf('133', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['97', '132'])).
% 0.21/0.57  thf('134', plain,
% 0.21/0.57      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('135', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['8', '10', '57', '45', '55', '56', '12'])).
% 0.21/0.57  thf('136', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 0.21/0.57  thf('137', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['133', '136'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
