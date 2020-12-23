%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gMjypn3yB1

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:57 EST 2020

% Result     : Theorem 3.14s
% Output     : Refutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 136 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  710 (2003 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X10 @ X9 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['20','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gMjypn3yB1
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.14/3.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.14/3.37  % Solved by: fo/fo7.sh
% 3.14/3.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.14/3.37  % done 1995 iterations in 2.879s
% 3.14/3.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.14/3.37  % SZS output start Refutation
% 3.14/3.37  thf(sk_B_type, type, sk_B: $i).
% 3.14/3.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.14/3.37  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.14/3.37  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.14/3.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.14/3.37  thf(sk_C_type, type, sk_C: $i).
% 3.14/3.37  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.14/3.37  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.14/3.37  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.14/3.37  thf(sk_A_type, type, sk_A: $i).
% 3.14/3.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.14/3.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.14/3.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.14/3.37  thf(t49_tops_1, conjecture,
% 3.14/3.37    (![A:$i]:
% 3.14/3.37     ( ( l1_pre_topc @ A ) =>
% 3.14/3.37       ( ![B:$i]:
% 3.14/3.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.14/3.37           ( ![C:$i]:
% 3.14/3.37             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.14/3.37               ( r1_tarski @
% 3.14/3.37                 ( k4_subset_1 @
% 3.14/3.37                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 3.14/3.37                   ( k1_tops_1 @ A @ C ) ) @ 
% 3.14/3.37                 ( k1_tops_1 @
% 3.14/3.37                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 3.14/3.37  thf(zf_stmt_0, negated_conjecture,
% 3.14/3.37    (~( ![A:$i]:
% 3.14/3.37        ( ( l1_pre_topc @ A ) =>
% 3.14/3.37          ( ![B:$i]:
% 3.14/3.37            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.14/3.37              ( ![C:$i]:
% 3.14/3.37                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.14/3.37                  ( r1_tarski @
% 3.14/3.37                    ( k4_subset_1 @
% 3.14/3.37                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 3.14/3.37                      ( k1_tops_1 @ A @ C ) ) @ 
% 3.14/3.37                    ( k1_tops_1 @
% 3.14/3.37                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 3.14/3.37    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 3.14/3.37  thf('0', plain,
% 3.14/3.37      (~ (r1_tarski @ 
% 3.14/3.37          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.14/3.37           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.14/3.37          (k1_tops_1 @ sk_A @ 
% 3.14/3.37           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('1', plain,
% 3.14/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('2', plain,
% 3.14/3.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf(redefinition_k4_subset_1, axiom,
% 3.14/3.37    (![A:$i,B:$i,C:$i]:
% 3.14/3.37     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.14/3.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.14/3.37       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.14/3.37  thf('3', plain,
% 3.14/3.37      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 3.14/3.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 3.14/3.37          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 3.14/3.37      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.14/3.37  thf('4', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.14/3.37            = (k2_xboole_0 @ sk_B @ X0))
% 3.14/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['2', '3'])).
% 3.14/3.37  thf('5', plain,
% 3.14/3.37      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 3.14/3.37         = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.37      inference('sup-', [status(thm)], ['1', '4'])).
% 3.14/3.37  thf('6', plain,
% 3.14/3.37      (~ (r1_tarski @ 
% 3.14/3.37          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.14/3.37           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.14/3.37          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.14/3.37      inference('demod', [status(thm)], ['0', '5'])).
% 3.14/3.37  thf('7', plain,
% 3.14/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf(dt_k1_tops_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( ( l1_pre_topc @ A ) & 
% 3.14/3.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.14/3.37       ( m1_subset_1 @
% 3.14/3.37         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.14/3.37  thf('8', plain,
% 3.14/3.37      (![X15 : $i, X16 : $i]:
% 3.14/3.37         (~ (l1_pre_topc @ X15)
% 3.14/3.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 3.14/3.37          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 3.14/3.37             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 3.14/3.37      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.14/3.37  thf('9', plain,
% 3.14/3.37      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.14/3.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.14/3.37        | ~ (l1_pre_topc @ sk_A))),
% 3.14/3.37      inference('sup-', [status(thm)], ['7', '8'])).
% 3.14/3.37  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('11', plain,
% 3.14/3.37      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.14/3.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('demod', [status(thm)], ['9', '10'])).
% 3.14/3.37  thf('12', plain,
% 3.14/3.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('13', plain,
% 3.14/3.37      (![X15 : $i, X16 : $i]:
% 3.14/3.37         (~ (l1_pre_topc @ X15)
% 3.14/3.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 3.14/3.37          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 3.14/3.37             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 3.14/3.37      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.14/3.37  thf('14', plain,
% 3.14/3.37      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.14/3.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.14/3.37        | ~ (l1_pre_topc @ sk_A))),
% 3.14/3.37      inference('sup-', [status(thm)], ['12', '13'])).
% 3.14/3.37  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('16', plain,
% 3.14/3.37      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.14/3.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('demod', [status(thm)], ['14', '15'])).
% 3.14/3.37  thf('17', plain,
% 3.14/3.37      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 3.14/3.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 3.14/3.37          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 3.14/3.37      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.14/3.37  thf('18', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 3.14/3.37            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 3.14/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['16', '17'])).
% 3.14/3.37  thf('19', plain,
% 3.14/3.37      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.14/3.37         (k1_tops_1 @ sk_A @ sk_C))
% 3.14/3.37         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 3.14/3.37      inference('sup-', [status(thm)], ['11', '18'])).
% 3.14/3.37  thf('20', plain,
% 3.14/3.37      (~ (r1_tarski @ 
% 3.14/3.37          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.14/3.37          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.14/3.37      inference('demod', [status(thm)], ['6', '19'])).
% 3.14/3.37  thf('21', plain,
% 3.14/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('22', plain,
% 3.14/3.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf(dt_k4_subset_1, axiom,
% 3.14/3.37    (![A:$i,B:$i,C:$i]:
% 3.14/3.37     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.14/3.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.14/3.37       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.14/3.37  thf('23', plain,
% 3.14/3.37      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.14/3.37          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 3.14/3.37          | (m1_subset_1 @ (k4_subset_1 @ X10 @ X9 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 3.14/3.37      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 3.14/3.37  thf('24', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 3.14/3.37           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.14/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['22', '23'])).
% 3.14/3.37  thf('25', plain,
% 3.14/3.37      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 3.14/3.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('sup-', [status(thm)], ['21', '24'])).
% 3.14/3.37  thf('26', plain,
% 3.14/3.37      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 3.14/3.37         = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.37      inference('sup-', [status(thm)], ['1', '4'])).
% 3.14/3.37  thf('27', plain,
% 3.14/3.37      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 3.14/3.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('demod', [status(thm)], ['25', '26'])).
% 3.14/3.37  thf('28', plain,
% 3.14/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf(t48_tops_1, axiom,
% 3.14/3.37    (![A:$i]:
% 3.14/3.37     ( ( l1_pre_topc @ A ) =>
% 3.14/3.37       ( ![B:$i]:
% 3.14/3.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.14/3.37           ( ![C:$i]:
% 3.14/3.37             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.14/3.37               ( ( r1_tarski @ B @ C ) =>
% 3.14/3.37                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.14/3.37  thf('29', plain,
% 3.14/3.37      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.14/3.37          | ~ (r1_tarski @ X17 @ X19)
% 3.14/3.37          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ (k1_tops_1 @ X18 @ X19))
% 3.14/3.37          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.14/3.37          | ~ (l1_pre_topc @ X18))),
% 3.14/3.37      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.14/3.37  thf('30', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (~ (l1_pre_topc @ sk_A)
% 3.14/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.14/3.37          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 3.14/3.37          | ~ (r1_tarski @ sk_C @ X0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['28', '29'])).
% 3.14/3.37  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('32', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.14/3.37          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 3.14/3.37          | ~ (r1_tarski @ sk_C @ X0))),
% 3.14/3.37      inference('demod', [status(thm)], ['30', '31'])).
% 3.14/3.37  thf('33', plain,
% 3.14/3.37      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))
% 3.14/3.37        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.14/3.37           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['27', '32'])).
% 3.14/3.37  thf(commutativity_k2_tarski, axiom,
% 3.14/3.37    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.14/3.37  thf('34', plain,
% 3.14/3.37      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 3.14/3.37      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.14/3.37  thf(l51_zfmisc_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.14/3.37  thf('35', plain,
% 3.14/3.37      (![X7 : $i, X8 : $i]:
% 3.14/3.37         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 3.14/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.14/3.37  thf('36', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]:
% 3.14/3.37         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('sup+', [status(thm)], ['34', '35'])).
% 3.14/3.37  thf('37', plain,
% 3.14/3.37      (![X7 : $i, X8 : $i]:
% 3.14/3.37         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 3.14/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.14/3.37  thf('38', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('sup+', [status(thm)], ['36', '37'])).
% 3.14/3.37  thf(t7_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.14/3.37  thf('39', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.14/3.37  thf('40', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.14/3.37      inference('sup+', [status(thm)], ['38', '39'])).
% 3.14/3.37  thf('41', plain,
% 3.14/3.37      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.14/3.37        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.14/3.37      inference('demod', [status(thm)], ['33', '40'])).
% 3.14/3.37  thf('42', plain,
% 3.14/3.37      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 3.14/3.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('demod', [status(thm)], ['25', '26'])).
% 3.14/3.37  thf('43', plain,
% 3.14/3.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('44', plain,
% 3.14/3.37      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.14/3.37          | ~ (r1_tarski @ X17 @ X19)
% 3.14/3.37          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ (k1_tops_1 @ X18 @ X19))
% 3.14/3.37          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.14/3.37          | ~ (l1_pre_topc @ X18))),
% 3.14/3.37      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.14/3.37  thf('45', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (~ (l1_pre_topc @ sk_A)
% 3.14/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.14/3.37          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 3.14/3.37          | ~ (r1_tarski @ sk_B @ X0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['43', '44'])).
% 3.14/3.37  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('47', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.14/3.37          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 3.14/3.37          | ~ (r1_tarski @ sk_B @ X0))),
% 3.14/3.37      inference('demod', [status(thm)], ['45', '46'])).
% 3.14/3.37  thf('48', plain,
% 3.14/3.37      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 3.14/3.37        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.14/3.37           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['42', '47'])).
% 3.14/3.37  thf('49', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.14/3.37  thf('50', plain,
% 3.14/3.37      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.14/3.37        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.14/3.37      inference('demod', [status(thm)], ['48', '49'])).
% 3.14/3.37  thf(t8_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i,C:$i]:
% 3.14/3.37     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 3.14/3.37       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.14/3.37  thf('51', plain,
% 3.14/3.37      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.14/3.37         (~ (r1_tarski @ X2 @ X3)
% 3.14/3.37          | ~ (r1_tarski @ X4 @ X3)
% 3.14/3.37          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 3.14/3.37      inference('cnf', [status(esa)], [t8_xboole_1])).
% 3.14/3.37  thf('52', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 3.14/3.37           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 3.14/3.37          | ~ (r1_tarski @ X0 @ 
% 3.14/3.37               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['50', '51'])).
% 3.14/3.37  thf('53', plain,
% 3.14/3.37      ((r1_tarski @ 
% 3.14/3.37        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.14/3.37        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.14/3.37      inference('sup-', [status(thm)], ['41', '52'])).
% 3.14/3.37  thf('54', plain, ($false), inference('demod', [status(thm)], ['20', '53'])).
% 3.14/3.37  
% 3.14/3.37  % SZS output end Refutation
% 3.14/3.37  
% 3.14/3.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
