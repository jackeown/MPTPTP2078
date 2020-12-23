%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pnbyhoijCp

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:19 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 147 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  851 (2180 expanded)
%              Number of equality atoms :   35 (  87 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
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

thf('13',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('16',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','19'])).

thf('21',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ X19 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ~ ! [X21: $i] :
          ( ( X21 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X21 @ sk_A )
          | ~ ( r1_tarski @ X21 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('35',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tops_1 @ X19 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X19 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['37'])).

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

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['45','56'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('58',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('65',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','33','34','36','38','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pnbyhoijCp
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 519 iterations in 0.179s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.63  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.44/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.44/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.63  thf(t86_tops_1, conjecture,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63           ( ( v2_tops_1 @ B @ A ) <=>
% 0.44/0.63             ( ![C:$i]:
% 0.44/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.44/0.63                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i]:
% 0.44/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.63          ( ![B:$i]:
% 0.44/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63              ( ( v2_tops_1 @ B @ A ) <=>
% 0.44/0.63                ( ![C:$i]:
% 0.44/0.63                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.44/0.63                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      (![X21 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ((X21) = (k1_xboole_0))
% 0.44/0.63          | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63          | ~ (r1_tarski @ X21 @ sk_B)
% 0.44/0.63          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      ((![X21 : $i]:
% 0.44/0.63          (((X21) = (k1_xboole_0))
% 0.44/0.63           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63           | ~ (r1_tarski @ X21 @ sk_B))) | 
% 0.44/0.63       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t44_tops_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_pre_topc @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.44/0.63  thf('3', plain,
% 0.44/0.63      (![X14 : $i, X15 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.44/0.63          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ X14)
% 0.44/0.63          | ~ (l1_pre_topc @ X15))),
% 0.44/0.63      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.44/0.63  thf('4', plain,
% 0.44/0.63      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.63  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('6', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.44/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(dt_k1_tops_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( ( l1_pre_topc @ A ) & 
% 0.44/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.63       ( m1_subset_1 @
% 0.44/0.63         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.63  thf('8', plain,
% 0.44/0.63      (![X10 : $i, X11 : $i]:
% 0.44/0.63         (~ (l1_pre_topc @ X10)
% 0.44/0.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.44/0.63          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 0.44/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.44/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.63  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('11', plain,
% 0.44/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.44/0.63  thf('12', plain,
% 0.44/0.63      ((![X21 : $i]:
% 0.44/0.63          (((X21) = (k1_xboole_0))
% 0.44/0.63           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63           | ~ (r1_tarski @ X21 @ sk_B)))
% 0.44/0.63         <= ((![X21 : $i]:
% 0.44/0.63                (((X21) = (k1_xboole_0))
% 0.44/0.63                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.44/0.63         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.44/0.63         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.44/0.63         <= ((![X21 : $i]:
% 0.44/0.63                (((X21) = (k1_xboole_0))
% 0.44/0.63                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.63  thf('14', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(fc9_tops_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.44/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.63       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.44/0.63  thf('15', plain,
% 0.44/0.63      (![X12 : $i, X13 : $i]:
% 0.44/0.63         (~ (l1_pre_topc @ X12)
% 0.44/0.63          | ~ (v2_pre_topc @ X12)
% 0.44/0.63          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.44/0.63          | (v3_pre_topc @ (k1_tops_1 @ X12 @ X13) @ X12))),
% 0.44/0.63      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.44/0.63  thf('16', plain,
% 0.44/0.63      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.44/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.63  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('19', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.44/0.63      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.44/0.63         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.44/0.63         <= ((![X21 : $i]:
% 0.44/0.63                (((X21) = (k1_xboole_0))
% 0.44/0.63                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.44/0.63      inference('demod', [status(thm)], ['13', '19'])).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.44/0.63         <= ((![X21 : $i]:
% 0.44/0.63                (((X21) = (k1_xboole_0))
% 0.44/0.63                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['6', '20'])).
% 0.44/0.63  thf('22', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t84_tops_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_pre_topc @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63           ( ( v2_tops_1 @ B @ A ) <=>
% 0.44/0.63             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.44/0.63  thf('23', plain,
% 0.44/0.63      (![X19 : $i, X20 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.63          | ((k1_tops_1 @ X20 @ X19) != (k1_xboole_0))
% 0.44/0.63          | (v2_tops_1 @ X19 @ X20)
% 0.44/0.63          | ~ (l1_pre_topc @ X20))),
% 0.44/0.63      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.44/0.63  thf('24', plain,
% 0.44/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | (v2_tops_1 @ sk_B @ sk_A)
% 0.44/0.63        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.63  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('26', plain,
% 0.44/0.63      (((v2_tops_1 @ sk_B @ sk_A)
% 0.44/0.63        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.44/0.63      inference('demod', [status(thm)], ['24', '25'])).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.44/0.63         <= ((![X21 : $i]:
% 0.44/0.63                (((X21) = (k1_xboole_0))
% 0.44/0.63                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['21', '26'])).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      (((v2_tops_1 @ sk_B @ sk_A))
% 0.44/0.63         <= ((![X21 : $i]:
% 0.44/0.63                (((X21) = (k1_xboole_0))
% 0.44/0.63                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.44/0.63      inference('simplify', [status(thm)], ['27'])).
% 0.44/0.63  thf('29', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('30', plain,
% 0.44/0.63      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['29'])).
% 0.44/0.63  thf('31', plain,
% 0.44/0.63      (~
% 0.44/0.63       (![X21 : $i]:
% 0.44/0.63          (((X21) = (k1_xboole_0))
% 0.44/0.63           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.44/0.63           | ~ (r1_tarski @ X21 @ sk_B))) | 
% 0.44/0.63       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['28', '30'])).
% 0.44/0.63  thf('32', plain,
% 0.44/0.63      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('33', plain,
% 0.44/0.63      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('split', [status(esa)], ['32'])).
% 0.44/0.63  thf('34', plain,
% 0.44/0.63      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('split', [status(esa)], ['29'])).
% 0.44/0.63  thf('35', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('36', plain,
% 0.44/0.63      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('split', [status(esa)], ['35'])).
% 0.44/0.63  thf('37', plain,
% 0.44/0.63      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('38', plain,
% 0.44/0.63      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.44/0.63       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('split', [status(esa)], ['37'])).
% 0.44/0.63  thf('39', plain,
% 0.44/0.63      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf('40', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('41', plain,
% 0.44/0.63      (![X19 : $i, X20 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.63          | ~ (v2_tops_1 @ X19 @ X20)
% 0.44/0.63          | ((k1_tops_1 @ X20 @ X19) = (k1_xboole_0))
% 0.44/0.63          | ~ (l1_pre_topc @ X20))),
% 0.44/0.63      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.44/0.63  thf('42', plain,
% 0.44/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.44/0.63  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.44/0.63  thf('45', plain,
% 0.44/0.63      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.44/0.63         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['39', '44'])).
% 0.44/0.63  thf('46', plain,
% 0.44/0.63      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.63      inference('split', [status(esa)], ['29'])).
% 0.44/0.63  thf('47', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('48', plain,
% 0.44/0.63      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['32'])).
% 0.44/0.63  thf('49', plain,
% 0.44/0.63      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('split', [status(esa)], ['37'])).
% 0.44/0.63  thf(t56_tops_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_pre_topc @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63           ( ![C:$i]:
% 0.44/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.44/0.63                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf('50', plain,
% 0.44/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.63          | ~ (v3_pre_topc @ X16 @ X17)
% 0.44/0.63          | ~ (r1_tarski @ X16 @ X18)
% 0.44/0.63          | (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.44/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.63          | ~ (l1_pre_topc @ X17))),
% 0.44/0.63      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.44/0.63  thf('51', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (~ (l1_pre_topc @ sk_A)
% 0.44/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.44/0.63           | ~ (r1_tarski @ sk_C @ X0)
% 0.44/0.63           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.44/0.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.63  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('53', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.44/0.63           | ~ (r1_tarski @ sk_C @ X0)
% 0.44/0.63           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.44/0.63         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('demod', [status(thm)], ['51', '52'])).
% 0.44/0.63  thf('54', plain,
% 0.44/0.63      ((![X0 : $i]:
% 0.44/0.63          (~ (r1_tarski @ sk_C @ X0)
% 0.44/0.63           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.44/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.44/0.63         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.44/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['48', '53'])).
% 0.44/0.63  thf('55', plain,
% 0.44/0.63      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.44/0.63         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.44/0.63         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.44/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['47', '54'])).
% 0.44/0.63  thf('56', plain,
% 0.44/0.63      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.44/0.63         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.44/0.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.44/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['46', '55'])).
% 0.44/0.63  thf('57', plain,
% 0.44/0.63      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.44/0.63         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.44/0.63             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.44/0.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.44/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('sup+', [status(thm)], ['45', '56'])).
% 0.44/0.63  thf(t4_subset_1, axiom,
% 0.44/0.63    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.44/0.63  thf('58', plain,
% 0.44/0.63      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.44/0.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.44/0.63  thf(t3_subset, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.63  thf('59', plain,
% 0.44/0.63      (![X4 : $i, X5 : $i]:
% 0.44/0.63         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.63  thf('60', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.44/0.63  thf(d10_xboole_0, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.63  thf('61', plain,
% 0.44/0.63      (![X0 : $i, X2 : $i]:
% 0.44/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.63  thf('62', plain,
% 0.44/0.63      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.63  thf('63', plain,
% 0.44/0.63      ((((sk_C) = (k1_xboole_0)))
% 0.44/0.63         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.44/0.63             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.44/0.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.44/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['57', '62'])).
% 0.44/0.63  thf('64', plain,
% 0.44/0.63      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.44/0.63      inference('split', [status(esa)], ['35'])).
% 0.44/0.63  thf('65', plain,
% 0.44/0.63      ((((sk_C) != (sk_C)))
% 0.44/0.63         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.44/0.63             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.44/0.63             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.44/0.63             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.44/0.63             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['63', '64'])).
% 0.44/0.63  thf('66', plain,
% 0.44/0.63      (~ ((r1_tarski @ sk_C @ sk_B)) | 
% 0.44/0.63       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.44/0.63       ~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.44/0.63       (((sk_C) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.44/0.63  thf('67', plain, ($false),
% 0.44/0.63      inference('sat_resolution*', [status(thm)],
% 0.44/0.63                ['1', '31', '33', '34', '36', '38', '66'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
