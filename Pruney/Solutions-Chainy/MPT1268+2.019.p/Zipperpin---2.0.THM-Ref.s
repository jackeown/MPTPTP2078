%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0IQkHZ3OpZ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 151 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  845 (2183 expanded)
%              Number of equality atoms :   37 (  90 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X19 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X19 @ sk_A )
      | ~ ( r1_tarski @ X19 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X10 @ X11 ) @ X10 ) ) ),
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
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','13','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ~ ! [X19: $i] :
          ( ( X19 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X19 @ sk_A )
          | ~ ( r1_tarski @ X19 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('34',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tops_1 @ X17 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['28'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['31'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

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

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ( r1_tarski @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['44','55'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('67',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','32','33','35','37','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0IQkHZ3OpZ
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 483 iterations in 0.095s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.55  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(t86_tops_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.55             ( ![C:$i]:
% 0.20/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.55                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55              ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.55                ( ![C:$i]:
% 0.20/0.55                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.55                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X19 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ((X19) = (k1_xboole_0))
% 0.20/0.55          | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55          | ~ (r1_tarski @ X19 @ sk_B)
% 0.20/0.55          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      ((![X19 : $i]:
% 0.20/0.55          (((X19) = (k1_xboole_0))
% 0.20/0.55           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55           | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55           | ~ (r1_tarski @ X19 @ sk_B))) | 
% 0.20/0.55       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k1_tops_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55       ( m1_subset_1 @
% 0.20/0.55         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | (m1_subset_1 @ (k1_tops_1 @ X8 @ X9) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((![X19 : $i]:
% 0.20/0.55          (((X19) = (k1_xboole_0))
% 0.20/0.55           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55           | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55           | ~ (r1_tarski @ X19 @ sk_B)))
% 0.20/0.55         <= ((![X19 : $i]:
% 0.20/0.55                (((X19) = (k1_xboole_0))
% 0.20/0.55                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.55         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.55         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.20/0.55         <= ((![X19 : $i]:
% 0.20/0.55                (((X19) = (k1_xboole_0))
% 0.20/0.55                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t44_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.55          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ X12)
% 0.20/0.55          | ~ (l1_pre_topc @ X13))),
% 0.20/0.55      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(fc9_tops_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X10)
% 0.20/0.55          | ~ (v2_pre_topc @ X10)
% 0.20/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.55          | (v3_pre_topc @ (k1_tops_1 @ X10 @ X11) @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.55         <= ((![X19 : $i]:
% 0.20/0.55                (((X19) = (k1_xboole_0))
% 0.20/0.55                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['8', '13', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t84_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.55             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | ((k1_tops_1 @ X18 @ X17) != (k1_xboole_0))
% 0.20/0.55          | (v2_tops_1 @ X17 @ X18)
% 0.20/0.55          | ~ (l1_pre_topc @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | (v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.55        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (((v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.55        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.20/0.55         <= ((![X19 : $i]:
% 0.20/0.55                (((X19) = (k1_xboole_0))
% 0.20/0.55                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (((v2_tops_1 @ sk_B @ sk_A))
% 0.20/0.55         <= ((![X19 : $i]:
% 0.20/0.55                (((X19) = (k1_xboole_0))
% 0.20/0.55                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.55  thf('28', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (~
% 0.20/0.55       (![X19 : $i]:
% 0.20/0.55          (((X19) = (k1_xboole_0))
% 0.20/0.55           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55           | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.20/0.55           | ~ (r1_tarski @ X19 @ sk_B))) | 
% 0.20/0.55       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['28'])).
% 0.20/0.55  thf('34', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.55       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | ~ (v2_tops_1 @ X17 @ X18)
% 0.20/0.55          | ((k1_tops_1 @ X18 @ X17) = (k1_xboole_0))
% 0.20/0.55          | ~ (l1_pre_topc @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.55         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['28'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['31'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.55         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('split', [status(esa)], ['36'])).
% 0.20/0.55  thf(t56_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.55                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.55          | ~ (v3_pre_topc @ X14 @ X15)
% 0.20/0.55          | ~ (r1_tarski @ X14 @ X16)
% 0.20/0.55          | (r1_tarski @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.20/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.55          | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (~ (l1_pre_topc @ sk_A)
% 0.20/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.55           | ~ (r1_tarski @ sk_C @ X0)
% 0.20/0.55           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.20/0.55         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.55           | ~ (r1_tarski @ sk_C @ X0)
% 0.20/0.55           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.20/0.55         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (~ (r1_tarski @ sk_C @ X0)
% 0.20/0.55           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.55         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.55         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.20/0.55         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['46', '53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.55             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '54'])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.20/0.55         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.55             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.55             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['44', '55'])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('58', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.55      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.55  thf(l32_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X3 : $i, X5 : $i]:
% 0.20/0.55         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.55  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.55  thf(t36_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.55  thf('62', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.55      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X0 : $i, X2 : $i]:
% 0.20/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.55         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.55             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.55             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['56', '64'])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['34'])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      ((((sk_C) != (sk_C)))
% 0.20/0.55         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.55             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.55             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.55             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (~ ((r1_tarski @ sk_C @ sk_B)) | 
% 0.20/0.55       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.55       ~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.20/0.55       (((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.55  thf('69', plain, ($false),
% 0.20/0.55      inference('sat_resolution*', [status(thm)],
% 0.20/0.55                ['1', '30', '32', '33', '35', '37', '68'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
