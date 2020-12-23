%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qRUWZloIN5

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:10 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 214 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  914 (2998 expanded)
%              Number of equality atoms :   14 (  80 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t58_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) )
            = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ ( k2_pre_topc @ X10 @ X9 ) @ ( k2_pre_topc @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('20',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_tops_1 @ X14 @ ( k1_tops_1 @ X14 @ X15 ) )
        = ( k1_tops_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['18','36'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
 != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ ( k2_pre_topc @ X10 @ X9 ) @ ( k2_pre_topc @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ ( k2_pre_topc @ X5 @ X6 ) )
        = ( k2_pre_topc @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('59',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['41','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qRUWZloIN5
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 279 iterations in 0.209s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(t58_tops_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.46/0.66             ( k2_pre_topc @
% 0.46/0.66               A @ 
% 0.46/0.66               ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( l1_pre_topc @ A ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66              ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.46/0.66                ( k2_pre_topc @
% 0.46/0.66                  A @ 
% 0.46/0.66                  ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t58_tops_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_k1_tops_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( m1_subset_1 @
% 0.46/0.66         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X12)
% 0.46/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.66          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf(dt_k2_pre_topc, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( m1_subset_1 @
% 0.46/0.66         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X3)
% 0.46/0.66          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.46/0.66          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X12)
% 0.46/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.66          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (((m1_subset_1 @ 
% 0.46/0.66         (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      ((m1_subset_1 @ 
% 0.46/0.66        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf(t49_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( r1_tarski @ B @ C ) =>
% 0.46/0.66                 ( r1_tarski @
% 0.46/0.66                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.66          | ~ (r1_tarski @ X9 @ X11)
% 0.46/0.66          | (r1_tarski @ (k2_pre_topc @ X10 @ X9) @ (k2_pre_topc @ X10 @ X11))
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.66          | ~ (l1_pre_topc @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.66        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ 
% 0.46/0.66            (k1_tops_1 @ sk_A @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['12', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf(t48_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( r1_tarski @ B @ C ) =>
% 0.46/0.66                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.66          | ~ (r1_tarski @ X18 @ X20)
% 0.46/0.66          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ (k1_tops_1 @ X19 @ X20))
% 0.46/0.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.66          | ~ (l1_pre_topc @ X19))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66             (k1_tops_1 @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.66  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(projectivity_k1_tops_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X14)
% 0.46/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.66          | ((k1_tops_1 @ X14 @ (k1_tops_1 @ X14 @ X15))
% 0.46/0.66              = (k1_tops_1 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.66          = (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.66         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['26', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.66        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf(t48_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.46/0.66          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ X7))
% 0.46/0.66          | ~ (l1_pre_topc @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['30', '35'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66        (k2_pre_topc @ sk_A @ 
% 0.46/0.66         (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.66      inference('demod', [status(thm)], ['18', '36'])).
% 0.46/0.66  thf(d10_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X0 : $i, X2 : $i]:
% 0.46/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      ((~ (r1_tarski @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ 
% 0.46/0.66            (k1_tops_1 @ sk_A @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.66        | ((k2_pre_topc @ sk_A @ 
% 0.46/0.66            (k1_tops_1 @ sk_A @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.66            = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.66         != (k2_pre_topc @ sk_A @ 
% 0.46/0.66             (k1_tops_1 @ sk_A @ 
% 0.46/0.66              (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (~ (r1_tarski @ 
% 0.46/0.66          (k2_pre_topc @ sk_A @ 
% 0.46/0.66           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))) @ 
% 0.46/0.66          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(t44_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.66          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.46/0.66          | ~ (l1_pre_topc @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (r1_tarski @ 
% 0.46/0.66           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((r1_tarski @ 
% 0.46/0.66        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.46/0.66        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      ((m1_subset_1 @ 
% 0.46/0.66        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.66          | ~ (r1_tarski @ X9 @ X11)
% 0.46/0.66          | (r1_tarski @ (k2_pre_topc @ X10 @ X9) @ (k2_pre_topc @ X10 @ X11))
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.66          | ~ (l1_pre_topc @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_tarski @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ 
% 0.46/0.66              (k1_tops_1 @ sk_A @ 
% 0.46/0.66               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_tarski @ 
% 0.46/0.66               (k1_tops_1 @ sk_A @ 
% 0.46/0.66                (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.46/0.66               X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_tarski @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ 
% 0.46/0.66              (k1_tops_1 @ sk_A @ 
% 0.46/0.66               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_tarski @ 
% 0.46/0.66               (k1_tops_1 @ sk_A @ 
% 0.46/0.66                (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.46/0.66               X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (((r1_tarski @ 
% 0.46/0.66         (k2_pre_topc @ sk_A @ 
% 0.46/0.66          (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))) @ 
% 0.46/0.66         (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.66        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['46', '51'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf(projectivity_k2_pre_topc, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.46/0.66         ( k2_pre_topc @ A @ B ) ) ))).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X5)
% 0.46/0.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.46/0.66          | ((k2_pre_topc @ X5 @ (k2_pre_topc @ X5 @ X6))
% 0.46/0.66              = (k2_pre_topc @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.66          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.66         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      ((r1_tarski @ 
% 0.46/0.66        (k2_pre_topc @ sk_A @ 
% 0.46/0.66         (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))) @ 
% 0.46/0.66        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['52', '57', '58'])).
% 0.46/0.66  thf('60', plain, ($false), inference('demod', [status(thm)], ['41', '59'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
