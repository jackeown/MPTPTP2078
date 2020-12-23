%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cEA6hAz9AC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 145 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  847 (2176 expanded)
%              Number of equality atoms :   37 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X43: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X43 @ sk_A )
      | ~ ( r1_tarski @ X43 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X43: $i] :
        ( ( X43 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X43 @ sk_A )
        | ~ ( r1_tarski @ X43 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X34 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('4',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X43: $i] :
        ( ( X43 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X43 @ sk_A )
        | ~ ( r1_tarski @ X43 @ sk_B ) )
   <= ! [X43: $i] :
        ( ( X43 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X43 @ sk_A )
        | ~ ( r1_tarski @ X43 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X43: $i] :
        ( ( X43 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X43 @ sk_A )
        | ~ ( r1_tarski @ X43 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X37 @ X36 ) @ X36 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X43: $i] :
        ( ( X43 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X43 @ sk_A )
        | ~ ( r1_tarski @ X43 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X43: $i] :
        ( ( X43 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X43 @ sk_A )
        | ~ ( r1_tarski @ X43 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

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
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k1_tops_1 @ X42 @ X41 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
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
   <= ! [X43: $i] :
        ( ( X43 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X43 @ sk_A )
        | ~ ( r1_tarski @ X43 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X43: $i] :
        ( ( X43 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X43 @ sk_A )
        | ~ ( r1_tarski @ X43 @ sk_B ) ) ),
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
    ( ~ ! [X43: $i] :
          ( ( X43 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X43 @ sk_A )
          | ~ ( r1_tarski @ X43 @ sk_B ) )
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
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tops_1 @ X41 @ X42 )
      | ( ( k1_tops_1 @ X42 @ X41 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v3_pre_topc @ X38 @ X39 )
      | ~ ( r1_tarski @ X38 @ X40 )
      | ( r1_tarski @ X38 @ ( k1_tops_1 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,
    ( ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
      = sk_C )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('60',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('63',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','33','34','36','38','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cEA6hAz9AC
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 193 iterations in 0.075s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.50  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(t86_tops_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.50             ( ![C:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.50                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50              ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.50                ( ![C:$i]:
% 0.21/0.50                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.50                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X43 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ((X43) = (k1_xboole_0))
% 0.21/0.50          | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.50          | ~ (r1_tarski @ X43 @ sk_B)
% 0.21/0.50          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((![X43 : $i]:
% 0.21/0.50          (((X43) = (k1_xboole_0))
% 0.21/0.50           | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50           | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.50           | ~ (r1_tarski @ X43 @ sk_B))) | 
% 0.21/0.50       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(fc9_tops_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X34 : $i, X35 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X34)
% 0.21/0.50          | ~ (v2_pre_topc @ X34)
% 0.21/0.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.21/0.50          | (v3_pre_topc @ (k1_tops_1 @ X34 @ X35) @ X34))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k1_tops_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X32 : $i, X33 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X32)
% 0.21/0.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.50          | (m1_subset_1 @ (k1_tops_1 @ X32 @ X33) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((![X43 : $i]:
% 0.21/0.50          (((X43) = (k1_xboole_0))
% 0.21/0.50           | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50           | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.50           | ~ (r1_tarski @ X43 @ sk_B)))
% 0.21/0.50         <= ((![X43 : $i]:
% 0.21/0.50                (((X43) = (k1_xboole_0))
% 0.21/0.50                 | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50                 | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.50                 | ~ (r1_tarski @ X43 @ sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.50         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.50         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.50         <= ((![X43 : $i]:
% 0.21/0.50                (((X43) = (k1_xboole_0))
% 0.21/0.50                 | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50                 | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.50                 | ~ (r1_tarski @ X43 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t44_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X36 : $i, X37 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.21/0.50          | (r1_tarski @ (k1_tops_1 @ X37 @ X36) @ X36)
% 0.21/0.50          | ~ (l1_pre_topc @ X37))),
% 0.21/0.50      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.50         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.50         <= ((![X43 : $i]:
% 0.21/0.50                (((X43) = (k1_xboole_0))
% 0.21/0.50                 | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50                 | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.50                 | ~ (r1_tarski @ X43 @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.50         <= ((![X43 : $i]:
% 0.21/0.50                (((X43) = (k1_xboole_0))
% 0.21/0.50                 | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50                 | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.50                 | ~ (r1_tarski @ X43 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t84_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.50             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X41 : $i, X42 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.21/0.50          | ((k1_tops_1 @ X42 @ X41) != (k1_xboole_0))
% 0.21/0.50          | (v2_tops_1 @ X41 @ X42)
% 0.21/0.50          | ~ (l1_pre_topc @ X42))),
% 0.21/0.50      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.50        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (((v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.50        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.21/0.50         <= ((![X43 : $i]:
% 0.21/0.50                (((X43) = (k1_xboole_0))
% 0.21/0.50                 | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50                 | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.50                 | ~ (r1_tarski @ X43 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (((v2_tops_1 @ sk_B @ sk_A))
% 0.21/0.50         <= ((![X43 : $i]:
% 0.21/0.50                (((X43) = (k1_xboole_0))
% 0.21/0.50                 | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51                 | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.51                 | ~ (r1_tarski @ X43 @ sk_B))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.51  thf('29', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (~
% 0.21/0.51       (![X43 : $i]:
% 0.21/0.51          (((X43) = (k1_xboole_0))
% 0.21/0.51           | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51           | ~ (v3_pre_topc @ X43 @ sk_A)
% 0.21/0.51           | ~ (r1_tarski @ X43 @ sk_B))) | 
% 0.21/0.51       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['29'])).
% 0.21/0.51  thf('35', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.51       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X41 : $i, X42 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.21/0.51          | ~ (v2_tops_1 @ X41 @ X42)
% 0.21/0.51          | ((k1_tops_1 @ X42 @ X41) = (k1_xboole_0))
% 0.21/0.51          | ~ (l1_pre_topc @ X42))),
% 0.21/0.51      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.51        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.51        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.51         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['29'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['32'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.51         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('split', [status(esa)], ['37'])).
% 0.21/0.51  thf(t56_tops_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.21/0.51          | ~ (v3_pre_topc @ X38 @ X39)
% 0.21/0.51          | ~ (r1_tarski @ X38 @ X40)
% 0.21/0.51          | (r1_tarski @ X38 @ (k1_tops_1 @ X39 @ X40))
% 0.21/0.51          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.21/0.51          | ~ (l1_pre_topc @ X39))),
% 0.21/0.51      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (l1_pre_topc @ sk_A)
% 0.21/0.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.51           | ~ (r1_tarski @ sk_C @ X0)
% 0.21/0.51           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.21/0.51         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.51           | ~ (r1_tarski @ sk_C @ X0)
% 0.21/0.51           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.21/0.51         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (r1_tarski @ sk_C @ X0)
% 0.21/0.51           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.51         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '53'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.21/0.51         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.21/0.51         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.51         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.51             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.21/0.51         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.21/0.51             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.51             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['45', '56'])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((((k3_xboole_0 @ sk_C @ k1_xboole_0) = (sk_C)))
% 0.21/0.51         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.21/0.51             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.51             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf(t2_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((((k1_xboole_0) = (sk_C)))
% 0.21/0.51         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.21/0.51             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.51             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['35'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      ((((sk_C) != (sk_C)))
% 0.21/0.51         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.21/0.51             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.21/0.51             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.51             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (~ ((r1_tarski @ sk_C @ sk_B)) | 
% 0.21/0.51       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.51       ~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.21/0.51       (((sk_C) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.51  thf('65', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)],
% 0.21/0.51                ['1', '31', '33', '34', '36', '38', '64'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
