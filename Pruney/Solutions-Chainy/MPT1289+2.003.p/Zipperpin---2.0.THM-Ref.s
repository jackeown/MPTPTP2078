%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iq6IVvTD9s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:59 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 439 expanded)
%              Number of leaves         :   21 ( 129 expanded)
%              Depth                    :   17
%              Number of atoms          : 1574 (6010 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t111_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A )
              & ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A )
                & ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t111_tops_1])).

thf('0',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) @ X12 )
      | ~ ( r1_tarski @ X12 @ ( k2_pre_topc @ X13 @ ( k1_tops_1 @ X13 @ X12 ) ) )
      | ( v4_tops_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ ( k2_pre_topc @ X5 @ X6 ) )
        = ( k2_pre_topc @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ ( k2_pre_topc @ X10 @ X9 ) @ ( k2_pre_topc @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('52',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ ( k2_pre_topc @ X10 @ X9 ) @ ( k2_pre_topc @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ ( k2_pre_topc @ X5 @ X6 ) )
        = ( k2_pre_topc @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('64',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_tops_1 @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_pre_topc @ X13 @ ( k1_tops_1 @ X13 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','73'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('75',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('79',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['76','85'])).

thf('87',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','86'])).

thf('88',plain,(
    v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['21','87'])).

thf('89',plain,
    ( ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,(
    v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,(
    ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('95',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) @ X12 )
      | ~ ( r1_tarski @ X12 @ ( k2_pre_topc @ X13 @ ( k1_tops_1 @ X13 @ X12 ) ) )
      | ( v4_tops_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X16 @ ( k1_tops_1 @ X16 @ X17 ) )
        = ( k1_tops_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('101',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('105',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','103','108'])).

thf('110',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['76','85'])).

thf('111',plain,
    ( ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_tops_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('114',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('119',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('123',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X16 @ ( k1_tops_1 @ X16 @ X17 ) )
        = ( k1_tops_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('124',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121','126'])).

thf('128',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['117','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['111','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['93','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iq6IVvTD9s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 282 iterations in 0.180s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.64  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.64  thf(t111_tops_1, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( ( v4_tops_1 @ B @ A ) =>
% 0.45/0.64             ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A ) & 
% 0.45/0.64               ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( l1_pre_topc @ A ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64              ( ( v4_tops_1 @ B @ A ) =>
% 0.45/0.64                ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A ) & 
% 0.45/0.64                  ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t111_tops_1])).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      ((~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      ((~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A))
% 0.45/0.64         <= (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_k2_pre_topc, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64       ( m1_subset_1 @
% 0.45/0.64         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X3)
% 0.45/0.64          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.45/0.64          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.64  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf(d6_tops_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( ( v4_tops_1 @ B @ A ) <=>
% 0.45/0.64             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.45/0.64               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.64          | ~ (r1_tarski @ (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)) @ X12)
% 0.45/0.64          | ~ (r1_tarski @ X12 @ (k2_pre_topc @ X13 @ (k1_tops_1 @ X13 @ X12)))
% 0.45/0.64          | (v4_tops_1 @ X12 @ X13)
% 0.45/0.64          | ~ (l1_pre_topc @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ 
% 0.45/0.64              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.45/0.64        | ~ (r1_tarski @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ 
% 0.45/0.64              (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(projectivity_k2_pre_topc, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.45/0.64         ( k2_pre_topc @ A @ B ) ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X5)
% 0.45/0.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.45/0.64          | ((k2_pre_topc @ X5 @ (k2_pre_topc @ X5 @ X6))
% 0.45/0.64              = (k2_pre_topc @ X5 @ X6)))),
% 0.45/0.64      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.45/0.64          = (k2_pre_topc @ sk_A @ sk_B))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.45/0.64         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ 
% 0.45/0.64              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.45/0.64        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['8', '9', '14'])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf(t44_tops_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.64          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 0.45/0.64          | ~ (l1_pre_topc @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64           (k2_pre_topc @ sk_A @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64        (k2_pre_topc @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ 
% 0.45/0.64              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['15', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf(dt_k1_tops_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64       ( m1_subset_1 @
% 0.45/0.64         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X14)
% 0.45/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.64          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X14)
% 0.45/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.64          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.64  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf(t49_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64               ( ( r1_tarski @ B @ C ) =>
% 0.45/0.64                 ( r1_tarski @
% 0.45/0.64                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.64          | ~ (r1_tarski @ X9 @ X11)
% 0.45/0.64          | (r1_tarski @ (k2_pre_topc @ X10 @ X9) @ (k2_pre_topc @ X10 @ X11))
% 0.45/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.64          | ~ (l1_pre_topc @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ sk_A)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.64  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.45/0.64        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64           (k2_pre_topc @ sk_A @ 
% 0.45/0.64            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['26', '35'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t48_tops_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64               ( ( r1_tarski @ B @ C ) =>
% 0.45/0.64                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.64          | ~ (r1_tarski @ X20 @ X22)
% 0.45/0.64          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ (k1_tops_1 @ X21 @ X22))
% 0.45/0.64          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.64          | ~ (l1_pre_topc @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ sk_A)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ sk_B @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.64  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ sk_B @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 0.45/0.64        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['37', '42'])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t48_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.45/0.64          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ X7))
% 0.45/0.64          | ~ (l1_pre_topc @ X8))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.64  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('48', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['43', '48'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['36', '49'])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X3)
% 0.45/0.64          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.45/0.64          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.64  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('55', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.64          | ~ (r1_tarski @ X9 @ X11)
% 0.45/0.64          | (r1_tarski @ (k2_pre_topc @ X10 @ X9) @ (k2_pre_topc @ X10 @ X11))
% 0.45/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.64          | ~ (l1_pre_topc @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ sk_A)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ sk_B @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.64  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ sk_B @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['58', '59'])).
% 0.45/0.64  thf('61', plain,
% 0.45/0.64      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.64        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64           (k2_pre_topc @ sk_A @ 
% 0.45/0.64            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['55', '60'])).
% 0.45/0.64  thf('62', plain,
% 0.45/0.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X5)
% 0.45/0.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.45/0.64          | ((k2_pre_topc @ X5 @ (k2_pre_topc @ X5 @ X6))
% 0.45/0.64              = (k2_pre_topc @ X5 @ X6)))),
% 0.45/0.64      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.45/0.64  thf('64', plain,
% 0.45/0.64      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.64          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.64         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.64        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['61', '66'])).
% 0.45/0.64  thf('68', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.64          | ~ (v4_tops_1 @ X12 @ X13)
% 0.45/0.64          | (r1_tarski @ X12 @ (k2_pre_topc @ X13 @ (k1_tops_1 @ X13 @ X12)))
% 0.45/0.64          | ~ (l1_pre_topc @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.64        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.64  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('72', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('73', plain,
% 0.45/0.64      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.45/0.64  thf('74', plain,
% 0.45/0.64      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '73'])).
% 0.45/0.64  thf(d10_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('75', plain,
% 0.45/0.64      (![X0 : $i, X2 : $i]:
% 0.45/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('76', plain,
% 0.45/0.64      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64           (k2_pre_topc @ sk_A @ sk_B))
% 0.45/0.64        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.64            = (k2_pre_topc @ sk_A @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.64  thf('77', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('78', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('79', plain,
% 0.45/0.64      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.45/0.64        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64           (k2_pre_topc @ sk_A @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.64  thf('80', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('81', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.64          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 0.45/0.64          | ~ (l1_pre_topc @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.45/0.64  thf('82', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['80', '81'])).
% 0.45/0.64  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('84', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.45/0.64      inference('demod', [status(thm)], ['82', '83'])).
% 0.45/0.64  thf('85', plain,
% 0.45/0.64      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.45/0.64        (k2_pre_topc @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['79', '84'])).
% 0.45/0.64  thf('86', plain,
% 0.45/0.64      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.64         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['76', '85'])).
% 0.45/0.64  thf('87', plain,
% 0.45/0.64      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['50', '86'])).
% 0.45/0.64  thf('88', plain, ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '87'])).
% 0.45/0.64  thf('89', plain,
% 0.45/0.64      ((~ (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))
% 0.45/0.64         <= (~ ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('90', plain, (((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.64  thf('91', plain,
% 0.45/0.64      (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)) | 
% 0.45/0.64       ~ ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('92', plain, (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.45/0.64  thf('93', plain, (~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['1', '92'])).
% 0.45/0.64  thf('94', plain,
% 0.45/0.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('95', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.64          | ~ (r1_tarski @ (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)) @ X12)
% 0.45/0.64          | ~ (r1_tarski @ X12 @ (k2_pre_topc @ X13 @ (k1_tops_1 @ X13 @ X12)))
% 0.45/0.64          | (v4_tops_1 @ X12 @ X13)
% 0.45/0.64          | ~ (l1_pre_topc @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.45/0.64  thf('96', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ 
% 0.45/0.64              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.64        | ~ (r1_tarski @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ 
% 0.45/0.64              (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.64  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('98', plain,
% 0.45/0.64      (((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64             (k2_pre_topc @ sk_A @ 
% 0.45/0.64              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.64        | ~ (r1_tarski @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ 
% 0.45/0.64              (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['96', '97'])).
% 0.45/0.64  thf('99', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(projectivity_k1_tops_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.45/0.64  thf('100', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X16)
% 0.45/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.45/0.64          | ((k1_tops_1 @ X16 @ (k1_tops_1 @ X16 @ X17))
% 0.45/0.64              = (k1_tops_1 @ X16 @ X17)))),
% 0.45/0.64      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.45/0.64  thf('101', plain,
% 0.45/0.64      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.64          = (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['99', '100'])).
% 0.45/0.64  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('103', plain,
% 0.45/0.64      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.64         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['101', '102'])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('105', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.45/0.64          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ X7))
% 0.45/0.64          | ~ (l1_pre_topc @ X8))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.45/0.64  thf('106', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['104', '105'])).
% 0.45/0.64  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('108', plain,
% 0.45/0.64      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.64        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['106', '107'])).
% 0.45/0.64  thf('109', plain,
% 0.45/0.64      (((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (r1_tarski @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ 
% 0.45/0.64              (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['98', '103', '108'])).
% 0.45/0.64  thf('110', plain,
% 0.45/0.64      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.64         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['76', '85'])).
% 0.45/0.64  thf('111', plain,
% 0.45/0.64      (((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['109', '110'])).
% 0.45/0.64  thf('112', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('113', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.64          | ~ (v4_tops_1 @ X12 @ X13)
% 0.45/0.64          | (r1_tarski @ (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)) @ X12)
% 0.45/0.64          | ~ (l1_pre_topc @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 0.45/0.64        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['112', '113'])).
% 0.45/0.64  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('116', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('117', plain,
% 0.45/0.64      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 0.45/0.64      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.45/0.64  thf('118', plain,
% 0.45/0.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('119', plain,
% 0.45/0.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.64          | ~ (r1_tarski @ X20 @ X22)
% 0.45/0.64          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ (k1_tops_1 @ X21 @ X22))
% 0.45/0.64          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.64          | ~ (l1_pre_topc @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.45/0.64  thf('120', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ sk_A)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ 
% 0.45/0.64              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64               X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['118', '119'])).
% 0.45/0.64  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('122', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf('123', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X16)
% 0.45/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.45/0.64          | ((k1_tops_1 @ X16 @ (k1_tops_1 @ X16 @ X17))
% 0.45/0.64              = (k1_tops_1 @ X16 @ X17)))),
% 0.45/0.64      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.45/0.64  thf('124', plain,
% 0.45/0.64      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.45/0.64          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['122', '123'])).
% 0.45/0.64  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('126', plain,
% 0.45/0.64      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.45/0.64         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.64  thf('127', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64             (k1_tops_1 @ sk_A @ X0))
% 0.45/0.64          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64               X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['120', '121', '126'])).
% 0.45/0.64  thf('128', plain,
% 0.45/0.64      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64         (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.64        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['117', '127'])).
% 0.45/0.64  thf('129', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('130', plain,
% 0.45/0.64      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.45/0.64        (k1_tops_1 @ sk_A @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['128', '129'])).
% 0.45/0.64  thf('131', plain, ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.45/0.64      inference('demod', [status(thm)], ['111', '130'])).
% 0.45/0.64  thf('132', plain, ($false), inference('demod', [status(thm)], ['93', '131'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
