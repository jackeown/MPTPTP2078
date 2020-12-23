%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bhXOvu76AW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:17 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 142 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  778 (1533 expanded)
%              Number of equality atoms :   24 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t73_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tops_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X8 @ ( k4_subset_1 @ X8 @ X9 @ X7 ) ) @ ( k3_subset_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('13',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k4_subset_1 @ X5 @ X4 @ X6 )
        = ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('18',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k4_subset_1 @ X5 @ X4 @ X6 )
        = ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ ( k2_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k2_tops_1 @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','32'])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_tops_1 @ X14 @ X13 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_pre_topc @ X14 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','35','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ ( k3_subset_1 @ X11 @ X10 ) )
      | ( r1_xboole_0 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bhXOvu76AW
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.41/2.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.41/2.65  % Solved by: fo/fo7.sh
% 2.41/2.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.41/2.65  % done 849 iterations in 2.196s
% 2.41/2.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.41/2.65  % SZS output start Refutation
% 2.41/2.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.41/2.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.41/2.65  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.41/2.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.41/2.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.41/2.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.41/2.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.41/2.65  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.41/2.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.41/2.65  thf(sk_A_type, type, sk_A: $i).
% 2.41/2.65  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.41/2.65  thf(sk_B_type, type, sk_B: $i).
% 2.41/2.65  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.41/2.65  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.41/2.65  thf(t73_tops_1, conjecture,
% 2.41/2.65    (![A:$i]:
% 2.41/2.65     ( ( l1_pre_topc @ A ) =>
% 2.41/2.65       ( ![B:$i]:
% 2.41/2.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.65           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 2.41/2.65  thf(zf_stmt_0, negated_conjecture,
% 2.41/2.65    (~( ![A:$i]:
% 2.41/2.65        ( ( l1_pre_topc @ A ) =>
% 2.41/2.65          ( ![B:$i]:
% 2.41/2.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.65              ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 2.41/2.65    inference('cnf.neg', [status(esa)], [t73_tops_1])).
% 2.41/2.65  thf('0', plain,
% 2.41/2.65      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf('1', plain,
% 2.41/2.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf(dt_k2_tops_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( ( l1_pre_topc @ A ) & 
% 2.41/2.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.41/2.65       ( m1_subset_1 @
% 2.41/2.65         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.41/2.65  thf('2', plain,
% 2.41/2.65      (![X17 : $i, X18 : $i]:
% 2.41/2.65         (~ (l1_pre_topc @ X17)
% 2.41/2.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 2.41/2.65          | (m1_subset_1 @ (k2_tops_1 @ X17 @ X18) @ 
% 2.41/2.65             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 2.41/2.65      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.41/2.65  thf('3', plain,
% 2.41/2.65      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.65        | ~ (l1_pre_topc @ sk_A))),
% 2.41/2.65      inference('sup-', [status(thm)], ['1', '2'])).
% 2.41/2.65  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf('5', plain,
% 2.41/2.65      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.65      inference('demod', [status(thm)], ['3', '4'])).
% 2.41/2.65  thf('6', plain,
% 2.41/2.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.65  thf(dt_k3_subset_1, axiom,
% 2.41/2.65    (![A:$i,B:$i]:
% 2.41/2.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.41/2.66       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.41/2.66  thf('7', plain,
% 2.41/2.66      (![X2 : $i, X3 : $i]:
% 2.41/2.66         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 2.41/2.66          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 2.41/2.66      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.41/2.66  thf('8', plain,
% 2.41/2.66      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('sup-', [status(thm)], ['6', '7'])).
% 2.41/2.66  thf(t41_subset_1, axiom,
% 2.41/2.66    (![A:$i,B:$i]:
% 2.41/2.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.41/2.66       ( ![C:$i]:
% 2.41/2.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.41/2.66           ( r1_tarski @
% 2.41/2.66             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 2.41/2.66             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 2.41/2.66  thf('9', plain,
% 2.41/2.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.41/2.66          | (r1_tarski @ (k3_subset_1 @ X8 @ (k4_subset_1 @ X8 @ X9 @ X7)) @ 
% 2.41/2.66             (k3_subset_1 @ X8 @ X9))
% 2.41/2.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 2.41/2.66      inference('cnf', [status(esa)], [t41_subset_1])).
% 2.41/2.66  thf('10', plain,
% 2.41/2.66      (![X0 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.66          | (r1_tarski @ 
% 2.41/2.66             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.41/2.66               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 2.41/2.66             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 2.41/2.66      inference('sup-', [status(thm)], ['8', '9'])).
% 2.41/2.66  thf('11', plain,
% 2.41/2.66      ((r1_tarski @ 
% 2.41/2.66        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 2.41/2.66        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.41/2.66      inference('sup-', [status(thm)], ['5', '10'])).
% 2.41/2.66  thf('12', plain,
% 2.41/2.66      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('sup-', [status(thm)], ['6', '7'])).
% 2.41/2.66  thf('13', plain,
% 2.41/2.66      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('demod', [status(thm)], ['3', '4'])).
% 2.41/2.66  thf(redefinition_k4_subset_1, axiom,
% 2.41/2.66    (![A:$i,B:$i,C:$i]:
% 2.41/2.66     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.41/2.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.41/2.66       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.41/2.66  thf('14', plain,
% 2.41/2.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.41/2.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5))
% 2.41/2.66          | ((k4_subset_1 @ X5 @ X4 @ X6) = (k2_xboole_0 @ X4 @ X6)))),
% 2.41/2.66      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.41/2.66  thf('15', plain,
% 2.41/2.66      (![X0 : $i]:
% 2.41/2.66         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 2.41/2.66            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 2.41/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.41/2.66      inference('sup-', [status(thm)], ['13', '14'])).
% 2.41/2.66  thf('16', plain,
% 2.41/2.66      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.41/2.66         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.41/2.66      inference('sup-', [status(thm)], ['12', '15'])).
% 2.41/2.66  thf('17', plain,
% 2.41/2.66      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('demod', [status(thm)], ['3', '4'])).
% 2.41/2.66  thf('18', plain,
% 2.41/2.66      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('sup-', [status(thm)], ['6', '7'])).
% 2.41/2.66  thf('19', plain,
% 2.41/2.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.41/2.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5))
% 2.41/2.66          | ((k4_subset_1 @ X5 @ X4 @ X6) = (k2_xboole_0 @ X4 @ X6)))),
% 2.41/2.66      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.41/2.66  thf('20', plain,
% 2.41/2.66      (![X0 : $i]:
% 2.41/2.66         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 2.41/2.66            = (k2_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0))
% 2.41/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.41/2.66      inference('sup-', [status(thm)], ['18', '19'])).
% 2.41/2.66  thf('21', plain,
% 2.41/2.66      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66         (k2_tops_1 @ sk_A @ sk_B))
% 2.41/2.66         = (k2_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.41/2.66      inference('sup-', [status(thm)], ['17', '20'])).
% 2.41/2.66  thf(commutativity_k2_xboole_0, axiom,
% 2.41/2.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.41/2.66  thf('22', plain,
% 2.41/2.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.41/2.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.41/2.66  thf('23', plain,
% 2.41/2.66      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66         (k2_tops_1 @ sk_A @ sk_B))
% 2.41/2.66         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.41/2.66      inference('demod', [status(thm)], ['21', '22'])).
% 2.41/2.66  thf('24', plain,
% 2.41/2.66      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('sup-', [status(thm)], ['6', '7'])).
% 2.41/2.66  thf(t65_tops_1, axiom,
% 2.41/2.66    (![A:$i]:
% 2.41/2.66     ( ( l1_pre_topc @ A ) =>
% 2.41/2.66       ( ![B:$i]:
% 2.41/2.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.66           ( ( k2_pre_topc @ A @ B ) =
% 2.41/2.66             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.41/2.66  thf('25', plain,
% 2.41/2.66      (![X21 : $i, X22 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.41/2.66          | ((k2_pre_topc @ X22 @ X21)
% 2.41/2.66              = (k4_subset_1 @ (u1_struct_0 @ X22) @ X21 @ 
% 2.41/2.66                 (k2_tops_1 @ X22 @ X21)))
% 2.41/2.66          | ~ (l1_pre_topc @ X22))),
% 2.41/2.66      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.41/2.66  thf('26', plain,
% 2.41/2.66      ((~ (l1_pre_topc @ sk_A)
% 2.41/2.66        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.41/2.66            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 2.41/2.66      inference('sup-', [status(thm)], ['24', '25'])).
% 2.41/2.66  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.66  thf('28', plain,
% 2.41/2.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.66  thf(t62_tops_1, axiom,
% 2.41/2.66    (![A:$i]:
% 2.41/2.66     ( ( l1_pre_topc @ A ) =>
% 2.41/2.66       ( ![B:$i]:
% 2.41/2.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.66           ( ( k2_tops_1 @ A @ B ) =
% 2.41/2.66             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 2.41/2.66  thf('29', plain,
% 2.41/2.66      (![X19 : $i, X20 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.41/2.66          | ((k2_tops_1 @ X20 @ X19)
% 2.41/2.66              = (k2_tops_1 @ X20 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19)))
% 2.41/2.66          | ~ (l1_pre_topc @ X20))),
% 2.41/2.66      inference('cnf', [status(esa)], [t62_tops_1])).
% 2.41/2.66  thf('30', plain,
% 2.41/2.66      ((~ (l1_pre_topc @ sk_A)
% 2.41/2.66        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.41/2.66            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 2.41/2.66      inference('sup-', [status(thm)], ['28', '29'])).
% 2.41/2.66  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.66  thf('32', plain,
% 2.41/2.66      (((k2_tops_1 @ sk_A @ sk_B)
% 2.41/2.66         = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.41/2.66      inference('demod', [status(thm)], ['30', '31'])).
% 2.41/2.66  thf('33', plain,
% 2.41/2.66      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.41/2.66         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.41/2.66            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.41/2.66      inference('demod', [status(thm)], ['26', '27', '32'])).
% 2.41/2.66  thf('34', plain,
% 2.41/2.66      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.41/2.66         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.41/2.66      inference('sup+', [status(thm)], ['23', '33'])).
% 2.41/2.66  thf('35', plain,
% 2.41/2.66      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.41/2.66         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.41/2.66      inference('demod', [status(thm)], ['16', '34'])).
% 2.41/2.66  thf('36', plain,
% 2.41/2.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.66  thf(d1_tops_1, axiom,
% 2.41/2.66    (![A:$i]:
% 2.41/2.66     ( ( l1_pre_topc @ A ) =>
% 2.41/2.66       ( ![B:$i]:
% 2.41/2.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.66           ( ( k1_tops_1 @ A @ B ) =
% 2.41/2.66             ( k3_subset_1 @
% 2.41/2.66               ( u1_struct_0 @ A ) @ 
% 2.41/2.66               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 2.41/2.66  thf('37', plain,
% 2.41/2.66      (![X13 : $i, X14 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 2.41/2.66          | ((k1_tops_1 @ X14 @ X13)
% 2.41/2.66              = (k3_subset_1 @ (u1_struct_0 @ X14) @ 
% 2.41/2.66                 (k2_pre_topc @ X14 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13))))
% 2.41/2.66          | ~ (l1_pre_topc @ X14))),
% 2.41/2.66      inference('cnf', [status(esa)], [d1_tops_1])).
% 2.41/2.66  thf('38', plain,
% 2.41/2.66      ((~ (l1_pre_topc @ sk_A)
% 2.41/2.66        | ((k1_tops_1 @ sk_A @ sk_B)
% 2.41/2.66            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66               (k2_pre_topc @ sk_A @ 
% 2.41/2.66                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 2.41/2.66      inference('sup-', [status(thm)], ['36', '37'])).
% 2.41/2.66  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.66  thf('40', plain,
% 2.41/2.66      (((k1_tops_1 @ sk_A @ sk_B)
% 2.41/2.66         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.66            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 2.41/2.66      inference('demod', [status(thm)], ['38', '39'])).
% 2.41/2.66  thf('41', plain,
% 2.41/2.66      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.41/2.66      inference('demod', [status(thm)], ['11', '35', '40'])).
% 2.41/2.66  thf('42', plain,
% 2.41/2.66      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('demod', [status(thm)], ['3', '4'])).
% 2.41/2.66  thf(t43_subset_1, axiom,
% 2.41/2.66    (![A:$i,B:$i]:
% 2.41/2.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.41/2.66       ( ![C:$i]:
% 2.41/2.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.41/2.66           ( ( r1_xboole_0 @ B @ C ) <=>
% 2.41/2.66             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.41/2.66  thf('43', plain,
% 2.41/2.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 2.41/2.66          | ~ (r1_tarski @ X12 @ (k3_subset_1 @ X11 @ X10))
% 2.41/2.66          | (r1_xboole_0 @ X12 @ X10)
% 2.41/2.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 2.41/2.66      inference('cnf', [status(esa)], [t43_subset_1])).
% 2.41/2.66  thf('44', plain,
% 2.41/2.66      (![X0 : $i]:
% 2.41/2.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.66          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 2.41/2.66          | ~ (r1_tarski @ X0 @ 
% 2.41/2.66               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 2.41/2.66      inference('sup-', [status(thm)], ['42', '43'])).
% 2.41/2.66  thf('45', plain,
% 2.41/2.66      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 2.41/2.66        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.41/2.66      inference('sup-', [status(thm)], ['41', '44'])).
% 2.41/2.66  thf('46', plain,
% 2.41/2.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.66  thf(dt_k1_tops_1, axiom,
% 2.41/2.66    (![A:$i,B:$i]:
% 2.41/2.66     ( ( ( l1_pre_topc @ A ) & 
% 2.41/2.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.41/2.66       ( m1_subset_1 @
% 2.41/2.66         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.41/2.66  thf('47', plain,
% 2.41/2.66      (![X15 : $i, X16 : $i]:
% 2.41/2.66         (~ (l1_pre_topc @ X15)
% 2.41/2.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.41/2.66          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 2.41/2.66             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 2.41/2.66      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.41/2.66  thf('48', plain,
% 2.41/2.66      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.66        | ~ (l1_pre_topc @ sk_A))),
% 2.41/2.66      inference('sup-', [status(thm)], ['46', '47'])).
% 2.41/2.66  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.66  thf('50', plain,
% 2.41/2.66      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.41/2.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.66      inference('demod', [status(thm)], ['48', '49'])).
% 2.41/2.66  thf('51', plain,
% 2.41/2.66      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 2.41/2.66      inference('demod', [status(thm)], ['45', '50'])).
% 2.41/2.66  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 2.41/2.66  
% 2.41/2.66  % SZS output end Refutation
% 2.41/2.66  
% 2.41/2.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
