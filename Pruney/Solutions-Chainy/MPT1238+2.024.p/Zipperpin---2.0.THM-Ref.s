%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uZJwrQcttD

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:59 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 133 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  715 (1995 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t49_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) @ ( k1_tops_1 @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) @ ( k1_tops_1 @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['20','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uZJwrQcttD
% 0.12/0.35  % Computer   : n011.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 13:07:27 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.58/2.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.58/2.78  % Solved by: fo/fo7.sh
% 2.58/2.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.58/2.78  % done 2052 iterations in 2.352s
% 2.58/2.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.58/2.78  % SZS output start Refutation
% 2.58/2.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.58/2.78  thf(sk_B_type, type, sk_B: $i).
% 2.58/2.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.58/2.78  thf(sk_A_type, type, sk_A: $i).
% 2.58/2.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.58/2.78  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.58/2.78  thf(sk_C_type, type, sk_C: $i).
% 2.58/2.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.58/2.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.58/2.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.58/2.78  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.58/2.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.58/2.78  thf(t49_tops_1, conjecture,
% 2.58/2.78    (![A:$i]:
% 2.58/2.78     ( ( l1_pre_topc @ A ) =>
% 2.58/2.78       ( ![B:$i]:
% 2.58/2.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.58/2.78           ( ![C:$i]:
% 2.58/2.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.58/2.78               ( r1_tarski @
% 2.58/2.78                 ( k4_subset_1 @
% 2.58/2.78                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 2.58/2.78                   ( k1_tops_1 @ A @ C ) ) @ 
% 2.58/2.78                 ( k1_tops_1 @
% 2.58/2.78                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 2.58/2.78  thf(zf_stmt_0, negated_conjecture,
% 2.58/2.78    (~( ![A:$i]:
% 2.58/2.78        ( ( l1_pre_topc @ A ) =>
% 2.58/2.78          ( ![B:$i]:
% 2.58/2.78            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.58/2.78              ( ![C:$i]:
% 2.58/2.78                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.58/2.78                  ( r1_tarski @
% 2.58/2.78                    ( k4_subset_1 @
% 2.58/2.78                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 2.58/2.78                      ( k1_tops_1 @ A @ C ) ) @ 
% 2.58/2.78                    ( k1_tops_1 @
% 2.58/2.78                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 2.58/2.78    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 2.58/2.78  thf('0', plain,
% 2.58/2.78      (~ (r1_tarski @ 
% 2.58/2.78          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.58/2.78           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 2.58/2.78          (k1_tops_1 @ sk_A @ 
% 2.58/2.78           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('1', plain,
% 2.58/2.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('2', plain,
% 2.58/2.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf(redefinition_k4_subset_1, axiom,
% 2.58/2.78    (![A:$i,B:$i,C:$i]:
% 2.58/2.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.58/2.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.58/2.78       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.58/2.78  thf('3', plain,
% 2.58/2.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.58/2.78         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.58/2.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 2.58/2.78          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 2.58/2.78      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.58/2.78  thf('4', plain,
% 2.58/2.78      (![X0 : $i]:
% 2.58/2.78         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.58/2.78            = (k2_xboole_0 @ sk_B @ X0))
% 2.58/2.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.58/2.78      inference('sup-', [status(thm)], ['2', '3'])).
% 2.58/2.78  thf('5', plain,
% 2.58/2.78      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 2.58/2.78         = (k2_xboole_0 @ sk_B @ sk_C))),
% 2.58/2.78      inference('sup-', [status(thm)], ['1', '4'])).
% 2.58/2.78  thf('6', plain,
% 2.58/2.78      (~ (r1_tarski @ 
% 2.58/2.78          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.58/2.78           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 2.58/2.78          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.58/2.78      inference('demod', [status(thm)], ['0', '5'])).
% 2.58/2.78  thf('7', plain,
% 2.58/2.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf(dt_k1_tops_1, axiom,
% 2.58/2.78    (![A:$i,B:$i]:
% 2.58/2.78     ( ( ( l1_pre_topc @ A ) & 
% 2.58/2.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.58/2.78       ( m1_subset_1 @
% 2.58/2.78         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.58/2.78  thf('8', plain,
% 2.58/2.78      (![X19 : $i, X20 : $i]:
% 2.58/2.78         (~ (l1_pre_topc @ X19)
% 2.58/2.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.58/2.78          | (m1_subset_1 @ (k1_tops_1 @ X19 @ X20) @ 
% 2.58/2.78             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 2.58/2.78      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.58/2.78  thf('9', plain,
% 2.58/2.78      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.58/2.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.58/2.78        | ~ (l1_pre_topc @ sk_A))),
% 2.58/2.78      inference('sup-', [status(thm)], ['7', '8'])).
% 2.58/2.78  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('11', plain,
% 2.58/2.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.58/2.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('demod', [status(thm)], ['9', '10'])).
% 2.58/2.78  thf('12', plain,
% 2.58/2.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('13', plain,
% 2.58/2.78      (![X19 : $i, X20 : $i]:
% 2.58/2.78         (~ (l1_pre_topc @ X19)
% 2.58/2.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.58/2.78          | (m1_subset_1 @ (k1_tops_1 @ X19 @ X20) @ 
% 2.58/2.78             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 2.58/2.78      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.58/2.78  thf('14', plain,
% 2.58/2.78      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.58/2.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.58/2.78        | ~ (l1_pre_topc @ sk_A))),
% 2.58/2.78      inference('sup-', [status(thm)], ['12', '13'])).
% 2.58/2.78  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('16', plain,
% 2.58/2.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.58/2.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('demod', [status(thm)], ['14', '15'])).
% 2.58/2.78  thf('17', plain,
% 2.58/2.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.58/2.78         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.58/2.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 2.58/2.78          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 2.58/2.78      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.58/2.78  thf('18', plain,
% 2.58/2.78      (![X0 : $i]:
% 2.58/2.78         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.58/2.78            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 2.58/2.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.58/2.78      inference('sup-', [status(thm)], ['16', '17'])).
% 2.58/2.78  thf('19', plain,
% 2.58/2.78      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.58/2.78         (k1_tops_1 @ sk_A @ sk_C))
% 2.58/2.78         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 2.58/2.78      inference('sup-', [status(thm)], ['11', '18'])).
% 2.58/2.78  thf('20', plain,
% 2.58/2.78      (~ (r1_tarski @ 
% 2.58/2.78          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 2.58/2.78          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.58/2.78      inference('demod', [status(thm)], ['6', '19'])).
% 2.58/2.78  thf('21', plain,
% 2.58/2.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('22', plain,
% 2.58/2.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf(dt_k4_subset_1, axiom,
% 2.58/2.78    (![A:$i,B:$i,C:$i]:
% 2.58/2.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.58/2.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.58/2.78       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.58/2.78  thf('23', plain,
% 2.58/2.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.58/2.78         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 2.58/2.78          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 2.58/2.78          | (m1_subset_1 @ (k4_subset_1 @ X14 @ X13 @ X15) @ 
% 2.58/2.78             (k1_zfmisc_1 @ X14)))),
% 2.58/2.78      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 2.58/2.78  thf('24', plain,
% 2.58/2.78      (![X0 : $i]:
% 2.58/2.78         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 2.58/2.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.58/2.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.58/2.78      inference('sup-', [status(thm)], ['22', '23'])).
% 2.58/2.78  thf('25', plain,
% 2.58/2.78      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.58/2.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('sup-', [status(thm)], ['21', '24'])).
% 2.58/2.78  thf('26', plain,
% 2.58/2.78      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 2.58/2.78         = (k2_xboole_0 @ sk_B @ sk_C))),
% 2.58/2.78      inference('sup-', [status(thm)], ['1', '4'])).
% 2.58/2.78  thf('27', plain,
% 2.58/2.78      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 2.58/2.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('demod', [status(thm)], ['25', '26'])).
% 2.58/2.78  thf('28', plain,
% 2.58/2.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf(t48_tops_1, axiom,
% 2.58/2.78    (![A:$i]:
% 2.58/2.78     ( ( l1_pre_topc @ A ) =>
% 2.58/2.78       ( ![B:$i]:
% 2.58/2.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.58/2.78           ( ![C:$i]:
% 2.58/2.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.58/2.78               ( ( r1_tarski @ B @ C ) =>
% 2.58/2.78                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.58/2.78  thf('29', plain,
% 2.58/2.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.58/2.78         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.58/2.78          | ~ (r1_tarski @ X21 @ X23)
% 2.58/2.78          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ (k1_tops_1 @ X22 @ X23))
% 2.58/2.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.58/2.78          | ~ (l1_pre_topc @ X22))),
% 2.58/2.78      inference('cnf', [status(esa)], [t48_tops_1])).
% 2.58/2.78  thf('30', plain,
% 2.58/2.78      (![X0 : $i]:
% 2.58/2.78         (~ (l1_pre_topc @ sk_A)
% 2.58/2.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.58/2.78          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 2.58/2.78          | ~ (r1_tarski @ sk_C @ X0))),
% 2.58/2.78      inference('sup-', [status(thm)], ['28', '29'])).
% 2.58/2.78  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('32', plain,
% 2.58/2.78      (![X0 : $i]:
% 2.58/2.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.58/2.78          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 2.58/2.78          | ~ (r1_tarski @ sk_C @ X0))),
% 2.58/2.78      inference('demod', [status(thm)], ['30', '31'])).
% 2.58/2.78  thf('33', plain,
% 2.58/2.78      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.58/2.78        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.58/2.78           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.58/2.78      inference('sup-', [status(thm)], ['27', '32'])).
% 2.58/2.78  thf(d10_xboole_0, axiom,
% 2.58/2.78    (![A:$i,B:$i]:
% 2.58/2.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.58/2.78  thf('34', plain,
% 2.58/2.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.58/2.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.58/2.78  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.58/2.78      inference('simplify', [status(thm)], ['34'])).
% 2.58/2.78  thf(t44_xboole_1, axiom,
% 2.58/2.78    (![A:$i,B:$i,C:$i]:
% 2.58/2.78     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 2.58/2.78       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.58/2.78  thf('36', plain,
% 2.58/2.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.58/2.78         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 2.58/2.78          | ~ (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7))),
% 2.58/2.78      inference('cnf', [status(esa)], [t44_xboole_1])).
% 2.58/2.78  thf('37', plain,
% 2.58/2.78      (![X0 : $i, X1 : $i]:
% 2.58/2.78         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.58/2.78      inference('sup-', [status(thm)], ['35', '36'])).
% 2.58/2.78  thf(t39_xboole_1, axiom,
% 2.58/2.78    (![A:$i,B:$i]:
% 2.58/2.78     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.58/2.78  thf('38', plain,
% 2.58/2.78      (![X3 : $i, X4 : $i]:
% 2.58/2.78         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 2.58/2.78           = (k2_xboole_0 @ X3 @ X4))),
% 2.58/2.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.58/2.78  thf('39', plain,
% 2.58/2.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 2.58/2.78      inference('demod', [status(thm)], ['37', '38'])).
% 2.58/2.78  thf('40', plain,
% 2.58/2.78      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.58/2.78        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.58/2.78      inference('demod', [status(thm)], ['33', '39'])).
% 2.58/2.78  thf('41', plain,
% 2.58/2.78      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 2.58/2.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('demod', [status(thm)], ['25', '26'])).
% 2.58/2.78  thf('42', plain,
% 2.58/2.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('43', plain,
% 2.58/2.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.58/2.78         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.58/2.78          | ~ (r1_tarski @ X21 @ X23)
% 2.58/2.78          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ (k1_tops_1 @ X22 @ X23))
% 2.58/2.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.58/2.78          | ~ (l1_pre_topc @ X22))),
% 2.58/2.78      inference('cnf', [status(esa)], [t48_tops_1])).
% 2.58/2.78  thf('44', plain,
% 2.58/2.78      (![X0 : $i]:
% 2.58/2.78         (~ (l1_pre_topc @ sk_A)
% 2.58/2.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.58/2.78          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 2.58/2.78          | ~ (r1_tarski @ sk_B @ X0))),
% 2.58/2.78      inference('sup-', [status(thm)], ['42', '43'])).
% 2.58/2.78  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 2.58/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.78  thf('46', plain,
% 2.58/2.78      (![X0 : $i]:
% 2.58/2.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.58/2.78          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 2.58/2.78          | ~ (r1_tarski @ sk_B @ X0))),
% 2.58/2.78      inference('demod', [status(thm)], ['44', '45'])).
% 2.58/2.78  thf('47', plain,
% 2.58/2.78      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.58/2.78        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.58/2.78           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.58/2.78      inference('sup-', [status(thm)], ['41', '46'])).
% 2.58/2.78  thf(t7_xboole_1, axiom,
% 2.58/2.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.58/2.78  thf('48', plain,
% 2.58/2.78      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 2.58/2.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.58/2.78  thf('49', plain,
% 2.58/2.78      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.58/2.78        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.58/2.78      inference('demod', [status(thm)], ['47', '48'])).
% 2.58/2.78  thf(t8_xboole_1, axiom,
% 2.58/2.78    (![A:$i,B:$i,C:$i]:
% 2.58/2.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.58/2.78       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.58/2.78  thf('50', plain,
% 2.58/2.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.58/2.78         (~ (r1_tarski @ X10 @ X11)
% 2.58/2.78          | ~ (r1_tarski @ X12 @ X11)
% 2.58/2.78          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 2.58/2.78      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.58/2.78  thf('51', plain,
% 2.58/2.78      (![X0 : $i]:
% 2.58/2.78         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 2.58/2.78           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 2.58/2.78          | ~ (r1_tarski @ X0 @ 
% 2.58/2.78               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.58/2.78      inference('sup-', [status(thm)], ['49', '50'])).
% 2.58/2.78  thf('52', plain,
% 2.58/2.78      ((r1_tarski @ 
% 2.58/2.78        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 2.58/2.78        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.58/2.78      inference('sup-', [status(thm)], ['40', '51'])).
% 2.58/2.78  thf('53', plain, ($false), inference('demod', [status(thm)], ['20', '52'])).
% 2.58/2.78  
% 2.58/2.78  % SZS output end Refutation
% 2.58/2.78  
% 2.58/2.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
