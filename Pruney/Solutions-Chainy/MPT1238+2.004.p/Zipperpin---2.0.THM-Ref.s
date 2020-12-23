%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YmoCWDz9Rw

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:57 EST 2020

% Result     : Theorem 12.64s
% Output     : Refutation 12.64s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 132 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  711 (1711 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('54',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['20','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YmoCWDz9Rw
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.64/12.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.64/12.87  % Solved by: fo/fo7.sh
% 12.64/12.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.64/12.87  % done 9121 iterations in 12.439s
% 12.64/12.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.64/12.87  % SZS output start Refutation
% 12.64/12.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.64/12.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.64/12.87  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 12.64/12.87  thf(sk_B_type, type, sk_B: $i).
% 12.64/12.87  thf(sk_A_type, type, sk_A: $i).
% 12.64/12.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.64/12.87  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 12.64/12.87  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 12.64/12.87  thf(sk_C_type, type, sk_C: $i).
% 12.64/12.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.64/12.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.64/12.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.64/12.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.64/12.87  thf(t49_tops_1, conjecture,
% 12.64/12.87    (![A:$i]:
% 12.64/12.87     ( ( l1_pre_topc @ A ) =>
% 12.64/12.87       ( ![B:$i]:
% 12.64/12.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.64/12.88           ( ![C:$i]:
% 12.64/12.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.64/12.88               ( r1_tarski @
% 12.64/12.88                 ( k4_subset_1 @
% 12.64/12.88                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 12.64/12.88                   ( k1_tops_1 @ A @ C ) ) @ 
% 12.64/12.88                 ( k1_tops_1 @
% 12.64/12.88                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 12.64/12.88  thf(zf_stmt_0, negated_conjecture,
% 12.64/12.88    (~( ![A:$i]:
% 12.64/12.88        ( ( l1_pre_topc @ A ) =>
% 12.64/12.88          ( ![B:$i]:
% 12.64/12.88            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.64/12.88              ( ![C:$i]:
% 12.64/12.88                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.64/12.88                  ( r1_tarski @
% 12.64/12.88                    ( k4_subset_1 @
% 12.64/12.88                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 12.64/12.88                      ( k1_tops_1 @ A @ C ) ) @ 
% 12.64/12.88                    ( k1_tops_1 @
% 12.64/12.88                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 12.64/12.88    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 12.64/12.88  thf('0', plain,
% 12.64/12.88      (~ (r1_tarski @ 
% 12.64/12.88          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 12.64/12.88           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 12.64/12.88          (k1_tops_1 @ sk_A @ 
% 12.64/12.88           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('1', plain,
% 12.64/12.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('2', plain,
% 12.64/12.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf(redefinition_k4_subset_1, axiom,
% 12.64/12.88    (![A:$i,B:$i,C:$i]:
% 12.64/12.88     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 12.64/12.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 12.64/12.88       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 12.64/12.88  thf('3', plain,
% 12.64/12.88      (![X9 : $i, X10 : $i, X11 : $i]:
% 12.64/12.88         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 12.64/12.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 12.64/12.88          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 12.64/12.88      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 12.64/12.88  thf('4', plain,
% 12.64/12.88      (![X0 : $i]:
% 12.64/12.88         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 12.64/12.88            = (k2_xboole_0 @ sk_B @ X0))
% 12.64/12.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.64/12.88      inference('sup-', [status(thm)], ['2', '3'])).
% 12.64/12.88  thf('5', plain,
% 12.64/12.88      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 12.64/12.88         = (k2_xboole_0 @ sk_B @ sk_C))),
% 12.64/12.88      inference('sup-', [status(thm)], ['1', '4'])).
% 12.64/12.88  thf('6', plain,
% 12.64/12.88      (~ (r1_tarski @ 
% 12.64/12.88          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 12.64/12.88           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 12.64/12.88          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 12.64/12.88      inference('demod', [status(thm)], ['0', '5'])).
% 12.64/12.88  thf('7', plain,
% 12.64/12.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf(dt_k1_tops_1, axiom,
% 12.64/12.88    (![A:$i,B:$i]:
% 12.64/12.88     ( ( ( l1_pre_topc @ A ) & 
% 12.64/12.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.64/12.88       ( m1_subset_1 @
% 12.64/12.88         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 12.64/12.88  thf('8', plain,
% 12.64/12.88      (![X15 : $i, X16 : $i]:
% 12.64/12.88         (~ (l1_pre_topc @ X15)
% 12.64/12.88          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 12.64/12.88          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 12.64/12.88             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 12.64/12.88      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 12.64/12.88  thf('9', plain,
% 12.64/12.88      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 12.64/12.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.64/12.88        | ~ (l1_pre_topc @ sk_A))),
% 12.64/12.88      inference('sup-', [status(thm)], ['7', '8'])).
% 12.64/12.88  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('11', plain,
% 12.64/12.88      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 12.64/12.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('demod', [status(thm)], ['9', '10'])).
% 12.64/12.88  thf('12', plain,
% 12.64/12.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('13', plain,
% 12.64/12.88      (![X15 : $i, X16 : $i]:
% 12.64/12.88         (~ (l1_pre_topc @ X15)
% 12.64/12.88          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 12.64/12.88          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 12.64/12.88             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 12.64/12.88      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 12.64/12.88  thf('14', plain,
% 12.64/12.88      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 12.64/12.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.64/12.88        | ~ (l1_pre_topc @ sk_A))),
% 12.64/12.88      inference('sup-', [status(thm)], ['12', '13'])).
% 12.64/12.88  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('16', plain,
% 12.64/12.88      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 12.64/12.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('demod', [status(thm)], ['14', '15'])).
% 12.64/12.88  thf('17', plain,
% 12.64/12.88      (![X9 : $i, X10 : $i, X11 : $i]:
% 12.64/12.88         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 12.64/12.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 12.64/12.88          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 12.64/12.88      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 12.64/12.88  thf('18', plain,
% 12.64/12.88      (![X0 : $i]:
% 12.64/12.88         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 12.64/12.88            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 12.64/12.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.64/12.88      inference('sup-', [status(thm)], ['16', '17'])).
% 12.64/12.88  thf('19', plain,
% 12.64/12.88      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 12.64/12.88         (k1_tops_1 @ sk_A @ sk_C))
% 12.64/12.88         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 12.64/12.88      inference('sup-', [status(thm)], ['11', '18'])).
% 12.64/12.88  thf('20', plain,
% 12.64/12.88      (~ (r1_tarski @ 
% 12.64/12.88          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 12.64/12.88          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 12.64/12.88      inference('demod', [status(thm)], ['6', '19'])).
% 12.64/12.88  thf('21', plain,
% 12.64/12.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf(t3_subset, axiom,
% 12.64/12.88    (![A:$i,B:$i]:
% 12.64/12.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.64/12.88  thf('22', plain,
% 12.64/12.88      (![X12 : $i, X13 : $i]:
% 12.64/12.88         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 12.64/12.88      inference('cnf', [status(esa)], [t3_subset])).
% 12.64/12.88  thf('23', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 12.64/12.88      inference('sup-', [status(thm)], ['21', '22'])).
% 12.64/12.88  thf('24', plain,
% 12.64/12.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('25', plain,
% 12.64/12.88      (![X12 : $i, X13 : $i]:
% 12.64/12.88         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 12.64/12.88      inference('cnf', [status(esa)], [t3_subset])).
% 12.64/12.88  thf('26', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 12.64/12.88      inference('sup-', [status(thm)], ['24', '25'])).
% 12.64/12.88  thf(t8_xboole_1, axiom,
% 12.64/12.88    (![A:$i,B:$i,C:$i]:
% 12.64/12.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 12.64/12.88       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 12.64/12.88  thf('27', plain,
% 12.64/12.88      (![X2 : $i, X3 : $i, X4 : $i]:
% 12.64/12.88         (~ (r1_tarski @ X2 @ X3)
% 12.64/12.88          | ~ (r1_tarski @ X4 @ X3)
% 12.64/12.88          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 12.64/12.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 12.64/12.88  thf('28', plain,
% 12.64/12.88      (![X0 : $i]:
% 12.64/12.88         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))
% 12.64/12.88          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('sup-', [status(thm)], ['26', '27'])).
% 12.64/12.88  thf('29', plain,
% 12.64/12.88      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (u1_struct_0 @ sk_A))),
% 12.64/12.88      inference('sup-', [status(thm)], ['23', '28'])).
% 12.64/12.88  thf('30', plain,
% 12.64/12.88      (![X12 : $i, X14 : $i]:
% 12.64/12.88         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 12.64/12.88      inference('cnf', [status(esa)], [t3_subset])).
% 12.64/12.88  thf('31', plain,
% 12.64/12.88      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 12.64/12.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('sup-', [status(thm)], ['29', '30'])).
% 12.64/12.88  thf('32', plain,
% 12.64/12.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf(t48_tops_1, axiom,
% 12.64/12.88    (![A:$i]:
% 12.64/12.88     ( ( l1_pre_topc @ A ) =>
% 12.64/12.88       ( ![B:$i]:
% 12.64/12.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.64/12.88           ( ![C:$i]:
% 12.64/12.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.64/12.88               ( ( r1_tarski @ B @ C ) =>
% 12.64/12.88                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 12.64/12.88  thf('33', plain,
% 12.64/12.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.64/12.88         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 12.64/12.88          | ~ (r1_tarski @ X17 @ X19)
% 12.64/12.88          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ (k1_tops_1 @ X18 @ X19))
% 12.64/12.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 12.64/12.88          | ~ (l1_pre_topc @ X18))),
% 12.64/12.88      inference('cnf', [status(esa)], [t48_tops_1])).
% 12.64/12.88  thf('34', plain,
% 12.64/12.88      (![X0 : $i]:
% 12.64/12.88         (~ (l1_pre_topc @ sk_A)
% 12.64/12.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.64/12.88          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 12.64/12.88          | ~ (r1_tarski @ sk_C @ X0))),
% 12.64/12.88      inference('sup-', [status(thm)], ['32', '33'])).
% 12.64/12.88  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('36', plain,
% 12.64/12.88      (![X0 : $i]:
% 12.64/12.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.64/12.88          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 12.64/12.88          | ~ (r1_tarski @ sk_C @ X0))),
% 12.64/12.88      inference('demod', [status(thm)], ['34', '35'])).
% 12.64/12.88  thf('37', plain,
% 12.64/12.88      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))
% 12.64/12.88        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 12.64/12.88           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 12.64/12.88      inference('sup-', [status(thm)], ['31', '36'])).
% 12.64/12.88  thf(commutativity_k2_tarski, axiom,
% 12.64/12.88    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 12.64/12.88  thf('38', plain,
% 12.64/12.88      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 12.64/12.88      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 12.64/12.88  thf(l51_zfmisc_1, axiom,
% 12.64/12.88    (![A:$i,B:$i]:
% 12.64/12.88     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 12.64/12.88  thf('39', plain,
% 12.64/12.88      (![X7 : $i, X8 : $i]:
% 12.64/12.88         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 12.64/12.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 12.64/12.88  thf('40', plain,
% 12.64/12.88      (![X0 : $i, X1 : $i]:
% 12.64/12.88         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 12.64/12.88      inference('sup+', [status(thm)], ['38', '39'])).
% 12.64/12.88  thf('41', plain,
% 12.64/12.88      (![X7 : $i, X8 : $i]:
% 12.64/12.88         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 12.64/12.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 12.64/12.88  thf('42', plain,
% 12.64/12.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.64/12.88      inference('sup+', [status(thm)], ['40', '41'])).
% 12.64/12.88  thf(t7_xboole_1, axiom,
% 12.64/12.88    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 12.64/12.88  thf('43', plain,
% 12.64/12.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 12.64/12.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.64/12.88  thf('44', plain,
% 12.64/12.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 12.64/12.88      inference('sup+', [status(thm)], ['42', '43'])).
% 12.64/12.88  thf('45', plain,
% 12.64/12.88      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 12.64/12.88        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 12.64/12.88      inference('demod', [status(thm)], ['37', '44'])).
% 12.64/12.88  thf('46', plain,
% 12.64/12.88      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 12.64/12.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('sup-', [status(thm)], ['29', '30'])).
% 12.64/12.88  thf('47', plain,
% 12.64/12.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('48', plain,
% 12.64/12.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.64/12.88         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 12.64/12.88          | ~ (r1_tarski @ X17 @ X19)
% 12.64/12.88          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ (k1_tops_1 @ X18 @ X19))
% 12.64/12.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 12.64/12.88          | ~ (l1_pre_topc @ X18))),
% 12.64/12.88      inference('cnf', [status(esa)], [t48_tops_1])).
% 12.64/12.88  thf('49', plain,
% 12.64/12.88      (![X0 : $i]:
% 12.64/12.88         (~ (l1_pre_topc @ sk_A)
% 12.64/12.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.64/12.88          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 12.64/12.88          | ~ (r1_tarski @ sk_B @ X0))),
% 12.64/12.88      inference('sup-', [status(thm)], ['47', '48'])).
% 12.64/12.88  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 12.64/12.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.64/12.88  thf('51', plain,
% 12.64/12.88      (![X0 : $i]:
% 12.64/12.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.64/12.88          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 12.64/12.88          | ~ (r1_tarski @ sk_B @ X0))),
% 12.64/12.88      inference('demod', [status(thm)], ['49', '50'])).
% 12.64/12.88  thf('52', plain,
% 12.64/12.88      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 12.64/12.88        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 12.64/12.88           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 12.64/12.88      inference('sup-', [status(thm)], ['46', '51'])).
% 12.64/12.88  thf('53', plain,
% 12.64/12.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 12.64/12.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.64/12.88  thf('54', plain,
% 12.64/12.88      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 12.64/12.88        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 12.64/12.88      inference('demod', [status(thm)], ['52', '53'])).
% 12.64/12.88  thf('55', plain,
% 12.64/12.88      (![X2 : $i, X3 : $i, X4 : $i]:
% 12.64/12.88         (~ (r1_tarski @ X2 @ X3)
% 12.64/12.88          | ~ (r1_tarski @ X4 @ X3)
% 12.64/12.88          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 12.64/12.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 12.64/12.88  thf('56', plain,
% 12.64/12.88      (![X0 : $i]:
% 12.64/12.88         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 12.64/12.88           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 12.64/12.88          | ~ (r1_tarski @ X0 @ 
% 12.64/12.88               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 12.64/12.88      inference('sup-', [status(thm)], ['54', '55'])).
% 12.64/12.88  thf('57', plain,
% 12.64/12.88      ((r1_tarski @ 
% 12.64/12.88        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 12.64/12.88        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 12.64/12.88      inference('sup-', [status(thm)], ['45', '56'])).
% 12.64/12.88  thf('58', plain, ($false), inference('demod', [status(thm)], ['20', '57'])).
% 12.64/12.88  
% 12.64/12.88  % SZS output end Refutation
% 12.64/12.88  
% 12.64/12.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
