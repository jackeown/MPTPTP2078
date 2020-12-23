%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H0rd4OlBJC

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:18 EST 2020

% Result     : Theorem 6.05s
% Output     : Refutation 6.05s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 165 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  763 (1842 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X9 @ ( k4_subset_1 @ X9 @ X10 @ X8 ) ) @ ( k3_subset_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k4_subset_1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ X18 )
        = ( k2_tops_1 @ X19 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','25'])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k1_tops_1 @ X15 @ X14 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k2_pre_topc @ X15 @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','27','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ( r1_xboole_0 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('39',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','25'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('46',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('48',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H0rd4OlBJC
% 0.16/0.38  % Computer   : n016.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 18:00:19 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 6.05/6.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.05/6.29  % Solved by: fo/fo7.sh
% 6.05/6.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.05/6.29  % done 1666 iterations in 5.845s
% 6.05/6.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.05/6.29  % SZS output start Refutation
% 6.05/6.29  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.05/6.29  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.05/6.29  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 6.05/6.29  thf(sk_B_type, type, sk_B: $i).
% 6.05/6.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.05/6.29  thf(sk_A_type, type, sk_A: $i).
% 6.05/6.29  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 6.05/6.29  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.05/6.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.05/6.29  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 6.05/6.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.05/6.29  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 6.05/6.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.05/6.29  thf(t73_tops_1, conjecture,
% 6.05/6.29    (![A:$i]:
% 6.05/6.29     ( ( l1_pre_topc @ A ) =>
% 6.05/6.29       ( ![B:$i]:
% 6.05/6.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.29           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 6.05/6.29  thf(zf_stmt_0, negated_conjecture,
% 6.05/6.29    (~( ![A:$i]:
% 6.05/6.29        ( ( l1_pre_topc @ A ) =>
% 6.05/6.29          ( ![B:$i]:
% 6.05/6.29            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.29              ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 6.05/6.29    inference('cnf.neg', [status(esa)], [t73_tops_1])).
% 6.05/6.29  thf('0', plain,
% 6.05/6.29      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf('1', plain,
% 6.05/6.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf(dt_k2_tops_1, axiom,
% 6.05/6.29    (![A:$i,B:$i]:
% 6.05/6.29     ( ( ( l1_pre_topc @ A ) & 
% 6.05/6.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.05/6.29       ( m1_subset_1 @
% 6.05/6.29         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.05/6.29  thf('2', plain,
% 6.05/6.29      (![X16 : $i, X17 : $i]:
% 6.05/6.29         (~ (l1_pre_topc @ X16)
% 6.05/6.29          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 6.05/6.29          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 6.05/6.29             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 6.05/6.29      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 6.05/6.29  thf('3', plain,
% 6.05/6.29      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.29        | ~ (l1_pre_topc @ sk_A))),
% 6.05/6.29      inference('sup-', [status(thm)], ['1', '2'])).
% 6.05/6.29  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf('5', plain,
% 6.05/6.29      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('demod', [status(thm)], ['3', '4'])).
% 6.05/6.29  thf('6', plain,
% 6.05/6.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf(dt_k3_subset_1, axiom,
% 6.05/6.29    (![A:$i,B:$i]:
% 6.05/6.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.05/6.29       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.05/6.29  thf('7', plain,
% 6.05/6.29      (![X3 : $i, X4 : $i]:
% 6.05/6.29         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 6.05/6.29          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 6.05/6.29      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 6.05/6.29  thf('8', plain,
% 6.05/6.29      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('sup-', [status(thm)], ['6', '7'])).
% 6.05/6.29  thf(t41_subset_1, axiom,
% 6.05/6.29    (![A:$i,B:$i]:
% 6.05/6.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.05/6.29       ( ![C:$i]:
% 6.05/6.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.05/6.29           ( r1_tarski @
% 6.05/6.29             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 6.05/6.29             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 6.05/6.29  thf('9', plain,
% 6.05/6.29      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 6.05/6.29          | (r1_tarski @ (k3_subset_1 @ X9 @ (k4_subset_1 @ X9 @ X10 @ X8)) @ 
% 6.05/6.29             (k3_subset_1 @ X9 @ X10))
% 6.05/6.29          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 6.05/6.29      inference('cnf', [status(esa)], [t41_subset_1])).
% 6.05/6.29  thf('10', plain,
% 6.05/6.29      (![X0 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.29          | (r1_tarski @ 
% 6.05/6.29             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.29              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 6.05/6.29               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 6.05/6.29             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 6.05/6.29      inference('sup-', [status(thm)], ['8', '9'])).
% 6.05/6.29  thf('11', plain,
% 6.05/6.29      ((r1_tarski @ 
% 6.05/6.29        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.29         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 6.05/6.29        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.29      inference('sup-', [status(thm)], ['5', '10'])).
% 6.05/6.29  thf('12', plain,
% 6.05/6.29      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('demod', [status(thm)], ['3', '4'])).
% 6.05/6.29  thf('13', plain,
% 6.05/6.29      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('sup-', [status(thm)], ['6', '7'])).
% 6.05/6.29  thf(commutativity_k4_subset_1, axiom,
% 6.05/6.29    (![A:$i,B:$i,C:$i]:
% 6.05/6.29     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 6.05/6.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.05/6.29       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 6.05/6.29  thf('14', plain,
% 6.05/6.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 6.05/6.29          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 6.05/6.29          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k4_subset_1 @ X1 @ X2 @ X0)))),
% 6.05/6.29      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 6.05/6.29  thf('15', plain,
% 6.05/6.29      (![X0 : $i]:
% 6.05/6.29         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.29            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 6.05/6.29            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 6.05/6.29               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 6.05/6.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.05/6.29      inference('sup-', [status(thm)], ['13', '14'])).
% 6.05/6.29  thf('16', plain,
% 6.05/6.29      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.29         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.29         (k2_tops_1 @ sk_A @ sk_B))
% 6.05/6.29         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 6.05/6.29      inference('sup-', [status(thm)], ['12', '15'])).
% 6.05/6.29  thf('17', plain,
% 6.05/6.29      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('sup-', [status(thm)], ['6', '7'])).
% 6.05/6.29  thf(t65_tops_1, axiom,
% 6.05/6.29    (![A:$i]:
% 6.05/6.29     ( ( l1_pre_topc @ A ) =>
% 6.05/6.29       ( ![B:$i]:
% 6.05/6.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.29           ( ( k2_pre_topc @ A @ B ) =
% 6.05/6.29             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 6.05/6.29  thf('18', plain,
% 6.05/6.29      (![X20 : $i, X21 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 6.05/6.29          | ((k2_pre_topc @ X21 @ X20)
% 6.05/6.29              = (k4_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 6.05/6.29                 (k2_tops_1 @ X21 @ X20)))
% 6.05/6.29          | ~ (l1_pre_topc @ X21))),
% 6.05/6.29      inference('cnf', [status(esa)], [t65_tops_1])).
% 6.05/6.29  thf('19', plain,
% 6.05/6.29      ((~ (l1_pre_topc @ sk_A)
% 6.05/6.29        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 6.05/6.29            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.29               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.29               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 6.05/6.29      inference('sup-', [status(thm)], ['17', '18'])).
% 6.05/6.29  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf('21', plain,
% 6.05/6.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf(t62_tops_1, axiom,
% 6.05/6.29    (![A:$i]:
% 6.05/6.29     ( ( l1_pre_topc @ A ) =>
% 6.05/6.29       ( ![B:$i]:
% 6.05/6.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.29           ( ( k2_tops_1 @ A @ B ) =
% 6.05/6.29             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 6.05/6.29  thf('22', plain,
% 6.05/6.29      (![X18 : $i, X19 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 6.05/6.29          | ((k2_tops_1 @ X19 @ X18)
% 6.05/6.29              = (k2_tops_1 @ X19 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18)))
% 6.05/6.29          | ~ (l1_pre_topc @ X19))),
% 6.05/6.29      inference('cnf', [status(esa)], [t62_tops_1])).
% 6.05/6.29  thf('23', plain,
% 6.05/6.29      ((~ (l1_pre_topc @ sk_A)
% 6.05/6.29        | ((k2_tops_1 @ sk_A @ sk_B)
% 6.05/6.29            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 6.05/6.29      inference('sup-', [status(thm)], ['21', '22'])).
% 6.05/6.29  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf('25', plain,
% 6.05/6.29      (((k2_tops_1 @ sk_A @ sk_B)
% 6.05/6.29         = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 6.05/6.29      inference('demod', [status(thm)], ['23', '24'])).
% 6.05/6.29  thf('26', plain,
% 6.05/6.29      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 6.05/6.29         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.29            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.29            (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.29      inference('demod', [status(thm)], ['19', '20', '25'])).
% 6.05/6.29  thf('27', plain,
% 6.05/6.29      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 6.05/6.29         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 6.05/6.29      inference('sup+', [status(thm)], ['16', '26'])).
% 6.05/6.29  thf('28', plain,
% 6.05/6.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf(d1_tops_1, axiom,
% 6.05/6.29    (![A:$i]:
% 6.05/6.29     ( ( l1_pre_topc @ A ) =>
% 6.05/6.29       ( ![B:$i]:
% 6.05/6.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.29           ( ( k1_tops_1 @ A @ B ) =
% 6.05/6.29             ( k3_subset_1 @
% 6.05/6.29               ( u1_struct_0 @ A ) @ 
% 6.05/6.29               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 6.05/6.29  thf('29', plain,
% 6.05/6.29      (![X14 : $i, X15 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 6.05/6.29          | ((k1_tops_1 @ X15 @ X14)
% 6.05/6.29              = (k3_subset_1 @ (u1_struct_0 @ X15) @ 
% 6.05/6.29                 (k2_pre_topc @ X15 @ (k3_subset_1 @ (u1_struct_0 @ X15) @ X14))))
% 6.05/6.29          | ~ (l1_pre_topc @ X15))),
% 6.05/6.29      inference('cnf', [status(esa)], [d1_tops_1])).
% 6.05/6.29  thf('30', plain,
% 6.05/6.29      ((~ (l1_pre_topc @ sk_A)
% 6.05/6.29        | ((k1_tops_1 @ sk_A @ sk_B)
% 6.05/6.29            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.29               (k2_pre_topc @ sk_A @ 
% 6.05/6.29                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 6.05/6.29      inference('sup-', [status(thm)], ['28', '29'])).
% 6.05/6.29  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.29  thf('32', plain,
% 6.05/6.29      (((k1_tops_1 @ sk_A @ sk_B)
% 6.05/6.29         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.29            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 6.05/6.29      inference('demod', [status(thm)], ['30', '31'])).
% 6.05/6.29  thf('33', plain,
% 6.05/6.29      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.29      inference('demod', [status(thm)], ['11', '27', '32'])).
% 6.05/6.29  thf('34', plain,
% 6.05/6.29      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('demod', [status(thm)], ['3', '4'])).
% 6.05/6.29  thf(t43_subset_1, axiom,
% 6.05/6.29    (![A:$i,B:$i]:
% 6.05/6.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.05/6.29       ( ![C:$i]:
% 6.05/6.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.05/6.29           ( ( r1_xboole_0 @ B @ C ) <=>
% 6.05/6.29             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 6.05/6.29  thf('35', plain,
% 6.05/6.29      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 6.05/6.29          | ~ (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X11))
% 6.05/6.29          | (r1_xboole_0 @ X13 @ X11)
% 6.05/6.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 6.05/6.29      inference('cnf', [status(esa)], [t43_subset_1])).
% 6.05/6.29  thf('36', plain,
% 6.05/6.29      (![X0 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.29          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 6.05/6.29          | ~ (r1_tarski @ X0 @ 
% 6.05/6.29               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 6.05/6.29      inference('sup-', [status(thm)], ['34', '35'])).
% 6.05/6.29  thf('37', plain,
% 6.05/6.29      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 6.05/6.29        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.05/6.29      inference('sup-', [status(thm)], ['33', '36'])).
% 6.05/6.29  thf('38', plain,
% 6.05/6.29      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('demod', [status(thm)], ['3', '4'])).
% 6.05/6.29  thf('39', plain,
% 6.05/6.29      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.29      inference('sup-', [status(thm)], ['6', '7'])).
% 6.05/6.29  thf(dt_k4_subset_1, axiom,
% 6.05/6.29    (![A:$i,B:$i,C:$i]:
% 6.05/6.29     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 6.05/6.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.05/6.29       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.05/6.29  thf('40', plain,
% 6.05/6.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.05/6.29         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 6.05/6.29          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6))
% 6.05/6.29          | (m1_subset_1 @ (k4_subset_1 @ X6 @ X5 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 6.05/6.29      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 6.05/6.30  thf('41', plain,
% 6.05/6.30      (![X0 : $i]:
% 6.05/6.30         ((m1_subset_1 @ 
% 6.05/6.30           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.30            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 6.05/6.30           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.05/6.30      inference('sup-', [status(thm)], ['39', '40'])).
% 6.05/6.30  thf('42', plain,
% 6.05/6.30      ((m1_subset_1 @ 
% 6.05/6.30        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.30         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.30         (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.30      inference('sup-', [status(thm)], ['38', '41'])).
% 6.05/6.30  thf('43', plain,
% 6.05/6.30      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 6.05/6.30         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.30            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.05/6.30            (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.30      inference('demod', [status(thm)], ['19', '20', '25'])).
% 6.05/6.30  thf('44', plain,
% 6.05/6.30      ((m1_subset_1 @ 
% 6.05/6.30        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 6.05/6.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.30      inference('demod', [status(thm)], ['42', '43'])).
% 6.05/6.30  thf('45', plain,
% 6.05/6.30      (![X3 : $i, X4 : $i]:
% 6.05/6.30         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 6.05/6.30          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 6.05/6.30      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 6.05/6.30  thf('46', plain,
% 6.05/6.30      ((m1_subset_1 @ 
% 6.05/6.30        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.30         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 6.05/6.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.30      inference('sup-', [status(thm)], ['44', '45'])).
% 6.05/6.30  thf('47', plain,
% 6.05/6.30      (((k1_tops_1 @ sk_A @ sk_B)
% 6.05/6.30         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.05/6.30            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 6.05/6.30      inference('demod', [status(thm)], ['30', '31'])).
% 6.05/6.30  thf('48', plain,
% 6.05/6.30      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.30      inference('demod', [status(thm)], ['46', '47'])).
% 6.05/6.30  thf('49', plain,
% 6.05/6.30      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 6.05/6.30      inference('demod', [status(thm)], ['37', '48'])).
% 6.05/6.30  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 6.05/6.30  
% 6.05/6.30  % SZS output end Refutation
% 6.05/6.30  
% 6.13/6.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
