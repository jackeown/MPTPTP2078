%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kYMMaRXJAj

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:18 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 144 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  832 (2161 expanded)
%              Number of equality atoms :   35 (  87 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X15 @ sk_A )
      | ~ ( r1_tarski @ X15 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X15: $i] :
        ( ( X15 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X15 @ sk_A )
        | ~ ( r1_tarski @ X15 @ sk_B ) )
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X9 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
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
    ( ! [X15: $i] :
        ( ( X15 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X15 @ sk_A )
        | ~ ( r1_tarski @ X15 @ sk_B ) )
   <= ! [X15: $i] :
        ( ( X15 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X15 @ sk_A )
        | ~ ( r1_tarski @ X15 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X15: $i] :
        ( ( X15 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X15 @ sk_A )
        | ~ ( r1_tarski @ X15 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ! [X15: $i] :
        ( ( X15 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X15 @ sk_A )
        | ~ ( r1_tarski @ X15 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('17',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X15: $i] :
        ( ( X15 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X15 @ sk_A )
        | ~ ( r1_tarski @ X15 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','20'])).

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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_tops_1 @ X14 @ X13 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
   <= ! [X15: $i] :
        ( ( X15 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X15 @ sk_A )
        | ~ ( r1_tarski @ X15 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X15: $i] :
        ( ( X15 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X15 @ sk_A )
        | ~ ( r1_tarski @ X15 @ sk_B ) ) ),
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
    ( ~ ! [X15: $i] :
          ( ( X15 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X15 @ sk_A )
          | ~ ( r1_tarski @ X15 @ sk_B ) )
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tops_1 @ X13 @ X14 )
      | ( ( k1_tops_1 @ X14 @ X13 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k1_tops_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('58',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kYMMaRXJAj
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.55  % Solved by: fo/fo7.sh
% 0.34/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.55  % done 178 iterations in 0.068s
% 0.34/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.55  % SZS output start Refutation
% 0.34/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.34/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.34/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.55  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.34/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.55  thf(t86_tops_1, conjecture,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.55       ( ![B:$i]:
% 0.34/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.55           ( ( v2_tops_1 @ B @ A ) <=>
% 0.34/0.55             ( ![C:$i]:
% 0.34/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.55                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.34/0.55                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.34/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.55    (~( ![A:$i]:
% 0.34/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.55          ( ![B:$i]:
% 0.34/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.55              ( ( v2_tops_1 @ B @ A ) <=>
% 0.34/0.55                ( ![C:$i]:
% 0.34/0.55                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.55                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.34/0.55                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.34/0.55    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.34/0.55  thf('0', plain,
% 0.34/0.55      (![X15 : $i]:
% 0.34/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55          | ((X15) = (k1_xboole_0))
% 0.34/0.55          | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55          | ~ (r1_tarski @ X15 @ sk_B)
% 0.34/0.55          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('1', plain,
% 0.34/0.55      ((![X15 : $i]:
% 0.34/0.55          (((X15) = (k1_xboole_0))
% 0.34/0.55           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55           | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55           | ~ (r1_tarski @ X15 @ sk_B))) | 
% 0.34/0.55       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('split', [status(esa)], ['0'])).
% 0.34/0.55  thf('2', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(t44_tops_1, axiom,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( l1_pre_topc @ A ) =>
% 0.34/0.55       ( ![B:$i]:
% 0.34/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.55           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.34/0.55  thf('3', plain,
% 0.34/0.55      (![X8 : $i, X9 : $i]:
% 0.34/0.55         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.34/0.55          | (r1_tarski @ (k1_tops_1 @ X9 @ X8) @ X8)
% 0.34/0.55          | ~ (l1_pre_topc @ X9))),
% 0.34/0.55      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.34/0.55  thf('4', plain,
% 0.34/0.55      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.34/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.55  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('6', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.34/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.34/0.55  thf('7', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(dt_k1_tops_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.34/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.55       ( m1_subset_1 @
% 0.34/0.55         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.34/0.55  thf('8', plain,
% 0.34/0.55      (![X4 : $i, X5 : $i]:
% 0.34/0.55         (~ (l1_pre_topc @ X4)
% 0.34/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.34/0.55          | (m1_subset_1 @ (k1_tops_1 @ X4 @ X5) @ 
% 0.34/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.34/0.55      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.34/0.55  thf('9', plain,
% 0.34/0.55      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.34/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.55  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('11', plain,
% 0.34/0.55      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.34/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.34/0.55  thf('12', plain,
% 0.34/0.55      ((![X15 : $i]:
% 0.34/0.55          (((X15) = (k1_xboole_0))
% 0.34/0.55           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55           | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55           | ~ (r1_tarski @ X15 @ sk_B)))
% 0.34/0.55         <= ((![X15 : $i]:
% 0.34/0.55                (((X15) = (k1_xboole_0))
% 0.34/0.55                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55                 | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55                 | ~ (r1_tarski @ X15 @ sk_B))))),
% 0.34/0.55      inference('split', [status(esa)], ['0'])).
% 0.34/0.55  thf('13', plain,
% 0.34/0.55      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.34/0.55         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.34/0.55         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.34/0.55         <= ((![X15 : $i]:
% 0.34/0.55                (((X15) = (k1_xboole_0))
% 0.34/0.55                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55                 | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55                 | ~ (r1_tarski @ X15 @ sk_B))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.55  thf('14', plain,
% 0.34/0.55      (((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.34/0.55         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)))
% 0.34/0.55         <= ((![X15 : $i]:
% 0.34/0.55                (((X15) = (k1_xboole_0))
% 0.34/0.55                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55                 | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55                 | ~ (r1_tarski @ X15 @ sk_B))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['6', '13'])).
% 0.34/0.55  thf('15', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(fc9_tops_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.34/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.55       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.34/0.55  thf('16', plain,
% 0.34/0.55      (![X6 : $i, X7 : $i]:
% 0.34/0.55         (~ (l1_pre_topc @ X6)
% 0.34/0.55          | ~ (v2_pre_topc @ X6)
% 0.34/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.34/0.55          | (v3_pre_topc @ (k1_tops_1 @ X6 @ X7) @ X6))),
% 0.34/0.55      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.34/0.55  thf('17', plain,
% 0.34/0.55      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.34/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.34/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.55  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('20', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.34/0.55      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.34/0.55  thf('21', plain,
% 0.34/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.34/0.55         <= ((![X15 : $i]:
% 0.34/0.55                (((X15) = (k1_xboole_0))
% 0.34/0.55                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55                 | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55                 | ~ (r1_tarski @ X15 @ sk_B))))),
% 0.34/0.55      inference('demod', [status(thm)], ['14', '20'])).
% 0.34/0.55  thf('22', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(t84_tops_1, axiom,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( l1_pre_topc @ A ) =>
% 0.34/0.55       ( ![B:$i]:
% 0.34/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.55           ( ( v2_tops_1 @ B @ A ) <=>
% 0.34/0.55             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.34/0.55  thf('23', plain,
% 0.34/0.55      (![X13 : $i, X14 : $i]:
% 0.34/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.34/0.55          | ((k1_tops_1 @ X14 @ X13) != (k1_xboole_0))
% 0.34/0.55          | (v2_tops_1 @ X13 @ X14)
% 0.34/0.55          | ~ (l1_pre_topc @ X14))),
% 0.34/0.55      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.34/0.55  thf('24', plain,
% 0.34/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.55        | (v2_tops_1 @ sk_B @ sk_A)
% 0.34/0.55        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.55  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('26', plain,
% 0.34/0.55      (((v2_tops_1 @ sk_B @ sk_A)
% 0.34/0.55        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.34/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.34/0.55  thf('27', plain,
% 0.34/0.55      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.34/0.55         <= ((![X15 : $i]:
% 0.34/0.55                (((X15) = (k1_xboole_0))
% 0.34/0.55                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55                 | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55                 | ~ (r1_tarski @ X15 @ sk_B))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['21', '26'])).
% 0.34/0.55  thf('28', plain,
% 0.34/0.55      (((v2_tops_1 @ sk_B @ sk_A))
% 0.34/0.55         <= ((![X15 : $i]:
% 0.34/0.55                (((X15) = (k1_xboole_0))
% 0.34/0.55                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55                 | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55                 | ~ (r1_tarski @ X15 @ sk_B))))),
% 0.34/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.34/0.55  thf('29', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('30', plain,
% 0.34/0.55      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.34/0.55      inference('split', [status(esa)], ['29'])).
% 0.34/0.55  thf('31', plain,
% 0.34/0.55      (~
% 0.34/0.55       (![X15 : $i]:
% 0.34/0.55          (((X15) = (k1_xboole_0))
% 0.34/0.55           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55           | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.34/0.55           | ~ (r1_tarski @ X15 @ sk_B))) | 
% 0.34/0.55       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('sup-', [status(thm)], ['28', '30'])).
% 0.34/0.55  thf('32', plain,
% 0.34/0.55      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('33', plain,
% 0.34/0.55      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('split', [status(esa)], ['32'])).
% 0.34/0.55  thf('34', plain,
% 0.34/0.55      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('split', [status(esa)], ['29'])).
% 0.34/0.55  thf('35', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('36', plain,
% 0.34/0.55      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('split', [status(esa)], ['35'])).
% 0.34/0.55  thf('37', plain,
% 0.34/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('38', plain,
% 0.34/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.34/0.55       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('split', [status(esa)], ['37'])).
% 0.34/0.55  thf('39', plain,
% 0.34/0.55      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.34/0.55      inference('split', [status(esa)], ['0'])).
% 0.34/0.55  thf('40', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('41', plain,
% 0.34/0.55      (![X13 : $i, X14 : $i]:
% 0.34/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.34/0.55          | ~ (v2_tops_1 @ X13 @ X14)
% 0.34/0.55          | ((k1_tops_1 @ X14 @ X13) = (k1_xboole_0))
% 0.34/0.55          | ~ (l1_pre_topc @ X14))),
% 0.34/0.55      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.34/0.55  thf('42', plain,
% 0.34/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.55        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.34/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.34/0.55  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('44', plain,
% 0.34/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.34/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.34/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.34/0.55  thf('45', plain,
% 0.34/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.34/0.55         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['39', '44'])).
% 0.34/0.55  thf('46', plain,
% 0.34/0.55      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.34/0.55      inference('split', [status(esa)], ['29'])).
% 0.34/0.55  thf('47', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('48', plain,
% 0.34/0.55      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.34/0.55      inference('split', [status(esa)], ['32'])).
% 0.34/0.55  thf('49', plain,
% 0.34/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.34/0.55         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('split', [status(esa)], ['37'])).
% 0.34/0.55  thf(t56_tops_1, axiom,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( l1_pre_topc @ A ) =>
% 0.34/0.55       ( ![B:$i]:
% 0.34/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.55           ( ![C:$i]:
% 0.34/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.55               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.34/0.55                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.34/0.55  thf('50', plain,
% 0.34/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.34/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.34/0.55          | ~ (v3_pre_topc @ X10 @ X11)
% 0.34/0.55          | ~ (r1_tarski @ X10 @ X12)
% 0.34/0.55          | (r1_tarski @ X10 @ (k1_tops_1 @ X11 @ X12))
% 0.34/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.34/0.55          | ~ (l1_pre_topc @ X11))),
% 0.34/0.55      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.34/0.55  thf('51', plain,
% 0.34/0.55      ((![X0 : $i]:
% 0.34/0.55          (~ (l1_pre_topc @ sk_A)
% 0.34/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.34/0.55           | ~ (r1_tarski @ sk_C @ X0)
% 0.34/0.55           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.34/0.55         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.34/0.55  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('53', plain,
% 0.34/0.55      ((![X0 : $i]:
% 0.34/0.55          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.55           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.34/0.55           | ~ (r1_tarski @ sk_C @ X0)
% 0.34/0.55           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.34/0.55         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.34/0.55  thf('54', plain,
% 0.34/0.55      ((![X0 : $i]:
% 0.34/0.55          (~ (r1_tarski @ sk_C @ X0)
% 0.34/0.55           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.34/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.34/0.55         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.34/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['48', '53'])).
% 0.34/0.55  thf('55', plain,
% 0.34/0.55      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.34/0.55         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.34/0.55         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.34/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['47', '54'])).
% 0.34/0.55  thf('56', plain,
% 0.34/0.55      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.34/0.55         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.34/0.55             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.34/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['46', '55'])).
% 0.34/0.55  thf('57', plain,
% 0.34/0.55      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.34/0.55         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.34/0.55             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.34/0.55             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.34/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('sup+', [status(thm)], ['45', '56'])).
% 0.34/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.34/0.55  thf('58', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.34/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.34/0.55  thf(d10_xboole_0, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.55  thf('59', plain,
% 0.34/0.55      (![X0 : $i, X2 : $i]:
% 0.34/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.34/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.55  thf('60', plain,
% 0.34/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.34/0.55  thf('61', plain,
% 0.34/0.55      ((((sk_C) = (k1_xboole_0)))
% 0.34/0.55         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.34/0.55             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.34/0.55             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.34/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['57', '60'])).
% 0.34/0.55  thf('62', plain,
% 0.34/0.55      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.34/0.55      inference('split', [status(esa)], ['35'])).
% 0.34/0.55  thf('63', plain,
% 0.34/0.55      ((((sk_C) != (sk_C)))
% 0.34/0.55         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.34/0.55             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.34/0.55             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.34/0.55             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.34/0.55             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.34/0.55  thf('64', plain,
% 0.34/0.55      (~ ((r1_tarski @ sk_C @ sk_B)) | 
% 0.34/0.55       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.34/0.55       ~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.34/0.55       (((sk_C) = (k1_xboole_0)))),
% 0.34/0.55      inference('simplify', [status(thm)], ['63'])).
% 0.34/0.55  thf('65', plain, ($false),
% 0.34/0.55      inference('sat_resolution*', [status(thm)],
% 0.34/0.55                ['1', '31', '33', '34', '36', '38', '64'])).
% 0.34/0.55  
% 0.34/0.55  % SZS output end Refutation
% 0.34/0.55  
% 0.34/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
