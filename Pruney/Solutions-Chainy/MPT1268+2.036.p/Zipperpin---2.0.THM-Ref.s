%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KLPLaxvOjM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 889 expanded)
%              Number of leaves         :   23 ( 236 expanded)
%              Depth                    :   23
%              Number of atoms          : 1269 (14302 expanded)
%              Number of equality atoms :   65 ( 604 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
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

thf('13',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( r1_tarski @ X23 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf('31',plain,
    ( ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

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

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_tops_1 @ X17 @ X16 )
       != X16 )
      | ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('34',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( l1_pre_topc @ X17 )
        | ~ ( v2_pre_topc @ X17 )
        | ( ( k1_tops_1 @ X17 @ X16 )
         != X16 )
        | ( v3_pre_topc @ X16 @ X17 ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( l1_pre_topc @ X17 )
        | ~ ( v2_pre_topc @ X17 )
        | ( ( k1_tops_1 @ X17 @ X16 )
         != X16 )
        | ( v3_pre_topc @ X16 @ X17 ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_tops_1 @ X17 @ X16 )
       != X16 )
      | ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('37',plain,
    ( ! [X14: $i,X15: $i] :
        ( ~ ( l1_pre_topc @ X14 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
   <= ! [X14: $i,X15: $i] :
        ( ~ ( l1_pre_topc @ X14 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X14: $i,X15: $i] :
        ( ~ ( l1_pre_topc @ X14 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ! [X14: $i,X15: $i] :
        ( ~ ( l1_pre_topc @ X14 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( l1_pre_topc @ X17 )
        | ~ ( v2_pre_topc @ X17 )
        | ( ( k1_tops_1 @ X17 @ X16 )
         != X16 )
        | ( v3_pre_topc @ X16 @ X17 ) )
    | ! [X14: $i,X15: $i] :
        ( ~ ( l1_pre_topc @ X14 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( ( k1_tops_1 @ X17 @ X16 )
       != X16 )
      | ( v3_pre_topc @ X16 @ X17 ) ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( ( k1_tops_1 @ X17 @ X16 )
       != X16 )
      | ( v3_pre_topc @ X16 @ X17 ) ) ),
    inference(simpl_trail,[status(thm)],['34','42'])).

thf('44',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k1_tops_1 @ X10 @ ( k1_tops_1 @ X10 @ X11 ) )
        = ( k1_tops_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','49','50','51'])).

thf('53',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','53'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('63',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('65',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('67',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('68',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_B )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('72',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('75',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('76',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['10','12','13','63','73','74','75'])).

thf('77',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['8','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['10','75','12','63','73','74','13'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','80'])).

thf('82',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('83',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['75','12','13','63','73','74','10'])).

thf('84',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['27'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['10','75','12','13','63','73','74'])).

thf('93',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['81','84','93'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
    | ( k1_xboole_0 = sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('97',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('98',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('100',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['10','75','13','63','73','74','12'])).

thf('101',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['98','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KLPLaxvOjM
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:40:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 456 iterations in 0.124s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
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
% 0.21/0.57  thf(t56_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.57                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (v3_pre_topc @ X18 @ X19)
% 0.21/0.57          | ~ (r1_tarski @ X18 @ X20)
% 0.21/0.57          | (r1_tarski @ X18 @ (k1_tops_1 @ X19 @ X20))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (l1_pre_topc @ sk_A)
% 0.21/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.57           | ~ (r1_tarski @ sk_C @ X0)
% 0.21/0.57           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.57  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.57           | ~ (r1_tarski @ sk_C @ X0)
% 0.21/0.57           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['7'])).
% 0.21/0.57  thf('9', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('11', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.57       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['1'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t3_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('16', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t44_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ X12)
% 0.21/0.57          | ~ (l1_pre_topc @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf(t1_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.57       ( r1_tarski @ A @ C ) ))).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.57          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | (r1_tarski @ X3 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.57          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X7 : $i, X9 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X23 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ((X23) = (k1_xboole_0))
% 0.21/0.57          | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57          | ~ (r1_tarski @ X23 @ sk_B)
% 0.21/0.57          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      ((![X23 : $i]:
% 0.21/0.57          (((X23) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X23 @ sk_B)))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.21/0.57      inference('split', [status(esa)], ['27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.57         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '28'])).
% 0.21/0.57  thf('30', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
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
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.57          | ((k1_tops_1 @ X17 @ X16) != (X16))
% 0.21/0.57          | (v3_pre_topc @ X16 @ X17)
% 0.21/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57          | ~ (l1_pre_topc @ X17)
% 0.21/0.57          | ~ (v2_pre_topc @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      ((![X16 : $i, X17 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57           | ~ (l1_pre_topc @ X17)
% 0.21/0.57           | ~ (v2_pre_topc @ X17)
% 0.21/0.57           | ((k1_tops_1 @ X17 @ X16) != (X16))
% 0.21/0.57           | (v3_pre_topc @ X16 @ X17)))
% 0.21/0.57         <= ((![X16 : $i, X17 : $i]:
% 0.21/0.57                (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57                 | ~ (l1_pre_topc @ X17)
% 0.21/0.57                 | ~ (v2_pre_topc @ X17)
% 0.21/0.57                 | ((k1_tops_1 @ X17 @ X16) != (X16))
% 0.21/0.57                 | (v3_pre_topc @ X16 @ X17))))),
% 0.21/0.57      inference('split', [status(esa)], ['33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.57          | ((k1_tops_1 @ X17 @ X16) != (X16))
% 0.21/0.57          | (v3_pre_topc @ X16 @ X17)
% 0.21/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57          | ~ (l1_pre_topc @ X17)
% 0.21/0.57          | ~ (v2_pre_topc @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      ((![X14 : $i, X15 : $i]:
% 0.21/0.57          (~ (l1_pre_topc @ X14)
% 0.21/0.57           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))))
% 0.21/0.57         <= ((![X14 : $i, X15 : $i]:
% 0.21/0.57                (~ (l1_pre_topc @ X14)
% 0.21/0.57                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))))),
% 0.21/0.57      inference('split', [status(esa)], ['36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A))
% 0.21/0.57         <= ((![X14 : $i, X15 : $i]:
% 0.21/0.57                (~ (l1_pre_topc @ X14)
% 0.21/0.57                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['35', '37'])).
% 0.21/0.57  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (~
% 0.21/0.57       (![X14 : $i, X15 : $i]:
% 0.21/0.57          (~ (l1_pre_topc @ X14)
% 0.21/0.57           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))))),
% 0.21/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      ((![X16 : $i, X17 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57           | ~ (l1_pre_topc @ X17)
% 0.21/0.57           | ~ (v2_pre_topc @ X17)
% 0.21/0.57           | ((k1_tops_1 @ X17 @ X16) != (X16))
% 0.21/0.57           | (v3_pre_topc @ X16 @ X17))) | 
% 0.21/0.57       (![X14 : $i, X15 : $i]:
% 0.21/0.57          (~ (l1_pre_topc @ X14)
% 0.21/0.57           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))))),
% 0.21/0.57      inference('split', [status(esa)], ['36'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      ((![X16 : $i, X17 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57           | ~ (l1_pre_topc @ X17)
% 0.21/0.57           | ~ (v2_pre_topc @ X17)
% 0.21/0.57           | ((k1_tops_1 @ X17 @ X16) != (X16))
% 0.21/0.57           | (v3_pre_topc @ X16 @ X17)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57          | ~ (l1_pre_topc @ X17)
% 0.21/0.57          | ~ (v2_pre_topc @ X17)
% 0.21/0.57          | ((k1_tops_1 @ X17 @ X16) != (X16))
% 0.21/0.57          | (v3_pre_topc @ X16 @ X17))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['34', '42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.21/0.57            != (k1_tops_1 @ sk_A @ sk_B))
% 0.21/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '43'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(projectivity_k1_tops_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.57       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X10)
% 0.21/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.57          | ((k1_tops_1 @ X10 @ (k1_tops_1 @ X10 @ X11))
% 0.21/0.57              = (k1_tops_1 @ X10 @ X11)))),
% 0.21/0.57      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.21/0.57          = (k1_tops_1 @ sk_A @ sk_B))
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.57  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.21/0.57         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.57  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '49', '50', '51'])).
% 0.21/0.57  thf('53', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '53'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t84_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.57             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.57          | ((k1_tops_1 @ X22 @ X21) != (k1_xboole_0))
% 0.21/0.57          | (v2_tops_1 @ X21 @ X22)
% 0.21/0.57          | ~ (l1_pre_topc @ X22))),
% 0.21/0.57      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | (v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.57  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['54', '59'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.21/0.57       ~
% 0.21/0.57       (![X23 : $i]:
% 0.21/0.57          (((X23) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X23 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['7'])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['1'])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      ((![X23 : $i]:
% 0.21/0.57          (((X23) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X23 @ sk_B)))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.21/0.57      inference('split', [status(esa)], ['27'])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      (((~ (r1_tarski @ sk_C @ sk_B)
% 0.21/0.57         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.21/0.57         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (((((sk_C) = (k1_xboole_0)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))) & 
% 0.21/0.57             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['65', '68'])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.57         <= ((![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))) & 
% 0.21/0.57             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.57             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['64', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      ((((sk_C) != (sk_C)))
% 0.21/0.57         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.21/0.57             (![X23 : $i]:
% 0.21/0.57                (((X23) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X23 @ sk_B))) & 
% 0.21/0.57             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.21/0.57             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (~
% 0.21/0.57       (![X23 : $i]:
% 0.21/0.57          (((X23) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 0.21/0.57       (((sk_C) = (k1_xboole_0))) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.57       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.57       ~ ((r1_tarski @ sk_C @ sk_B))),
% 0.21/0.57      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.21/0.57       (![X23 : $i]:
% 0.21/0.57          (((X23) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X23 @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['27'])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['7'])).
% 0.21/0.57  thf('76', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['10', '12', '13', '63', '73', '74', '75'])).
% 0.21/0.57  thf('77', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['8', '76'])).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.57           | ~ (r1_tarski @ sk_C @ X0)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '77'])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['10', '75', '12', '63', '73', '74', '13'])).
% 0.21/0.57  thf('80', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.57          | ~ (r1_tarski @ sk_C @ X0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.21/0.57        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '80'])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('83', plain, (((r1_tarski @ sk_C @ sk_B))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['75', '12', '13', '63', '73', '74', '10'])).
% 0.21/0.57  thf('84', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['27'])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.57          | ~ (v2_tops_1 @ X21 @ X22)
% 0.21/0.57          | ((k1_tops_1 @ X22 @ X21) = (k1_xboole_0))
% 0.21/0.57          | ~ (l1_pre_topc @ X22))),
% 0.21/0.57      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.57  thf('91', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['85', '90'])).
% 0.21/0.57  thf('92', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['10', '75', '12', '13', '63', '73', '74'])).
% 0.21/0.57  thf('93', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.21/0.57  thf('94', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.21/0.57      inference('demod', [status(thm)], ['81', '84', '93'])).
% 0.21/0.57  thf(d10_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      (![X0 : $i, X2 : $i]:
% 0.21/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      ((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.57  thf('97', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.57  thf('98', plain, (((k1_xboole_0) = (sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['11'])).
% 0.21/0.57  thf('100', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['10', '75', '13', '63', '73', '74', '12'])).
% 0.21/0.57  thf('101', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['99', '100'])).
% 0.21/0.57  thf('102', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['98', '101'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
