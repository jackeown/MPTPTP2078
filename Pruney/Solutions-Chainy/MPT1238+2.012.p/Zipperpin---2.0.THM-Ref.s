%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rrJvhHEY72

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:58 EST 2020

% Result     : Theorem 13.04s
% Output     : Refutation 13.04s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 124 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  672 (1664 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k4_subset_1 @ X8 @ X7 @ X9 )
        = ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k4_subset_1 @ X8 @ X7 @ X9 )
        = ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
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
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rrJvhHEY72
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 13.04/13.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.04/13.28  % Solved by: fo/fo7.sh
% 13.04/13.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.04/13.28  % done 9140 iterations in 12.814s
% 13.04/13.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.04/13.28  % SZS output start Refutation
% 13.04/13.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.04/13.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.04/13.28  thf(sk_C_type, type, sk_C: $i).
% 13.04/13.28  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 13.04/13.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 13.04/13.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.04/13.28  thf(sk_A_type, type, sk_A: $i).
% 13.04/13.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 13.04/13.28  thf(sk_B_type, type, sk_B: $i).
% 13.04/13.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.04/13.28  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 13.04/13.28  thf(t49_tops_1, conjecture,
% 13.04/13.28    (![A:$i]:
% 13.04/13.28     ( ( l1_pre_topc @ A ) =>
% 13.04/13.28       ( ![B:$i]:
% 13.04/13.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.04/13.28           ( ![C:$i]:
% 13.04/13.28             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.04/13.28               ( r1_tarski @
% 13.04/13.28                 ( k4_subset_1 @
% 13.04/13.28                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 13.04/13.28                   ( k1_tops_1 @ A @ C ) ) @ 
% 13.04/13.28                 ( k1_tops_1 @
% 13.04/13.28                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 13.04/13.28  thf(zf_stmt_0, negated_conjecture,
% 13.04/13.28    (~( ![A:$i]:
% 13.04/13.28        ( ( l1_pre_topc @ A ) =>
% 13.04/13.28          ( ![B:$i]:
% 13.04/13.28            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.04/13.28              ( ![C:$i]:
% 13.04/13.28                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.04/13.28                  ( r1_tarski @
% 13.04/13.28                    ( k4_subset_1 @
% 13.04/13.28                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 13.04/13.28                      ( k1_tops_1 @ A @ C ) ) @ 
% 13.04/13.28                    ( k1_tops_1 @
% 13.04/13.28                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 13.04/13.28    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 13.04/13.28  thf('0', plain,
% 13.04/13.28      (~ (r1_tarski @ 
% 13.04/13.28          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 13.04/13.28           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 13.04/13.28          (k1_tops_1 @ sk_A @ 
% 13.04/13.28           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('1', plain,
% 13.04/13.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('2', plain,
% 13.04/13.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf(redefinition_k4_subset_1, axiom,
% 13.04/13.28    (![A:$i,B:$i,C:$i]:
% 13.04/13.28     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 13.04/13.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 13.04/13.28       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 13.04/13.28  thf('3', plain,
% 13.04/13.28      (![X7 : $i, X8 : $i, X9 : $i]:
% 13.04/13.28         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 13.04/13.28          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 13.04/13.28          | ((k4_subset_1 @ X8 @ X7 @ X9) = (k2_xboole_0 @ X7 @ X9)))),
% 13.04/13.28      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 13.04/13.28  thf('4', plain,
% 13.04/13.28      (![X0 : $i]:
% 13.04/13.28         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 13.04/13.28            = (k2_xboole_0 @ sk_B @ X0))
% 13.04/13.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 13.04/13.28      inference('sup-', [status(thm)], ['2', '3'])).
% 13.04/13.28  thf('5', plain,
% 13.04/13.28      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 13.04/13.28         = (k2_xboole_0 @ sk_B @ sk_C))),
% 13.04/13.28      inference('sup-', [status(thm)], ['1', '4'])).
% 13.04/13.28  thf('6', plain,
% 13.04/13.28      (~ (r1_tarski @ 
% 13.04/13.28          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 13.04/13.28           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 13.04/13.28          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 13.04/13.28      inference('demod', [status(thm)], ['0', '5'])).
% 13.04/13.28  thf('7', plain,
% 13.04/13.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf(dt_k1_tops_1, axiom,
% 13.04/13.28    (![A:$i,B:$i]:
% 13.04/13.28     ( ( ( l1_pre_topc @ A ) & 
% 13.04/13.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 13.04/13.28       ( m1_subset_1 @
% 13.04/13.28         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 13.04/13.28  thf('8', plain,
% 13.04/13.28      (![X13 : $i, X14 : $i]:
% 13.04/13.28         (~ (l1_pre_topc @ X13)
% 13.04/13.28          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 13.04/13.28          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 13.04/13.28             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 13.04/13.28      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 13.04/13.28  thf('9', plain,
% 13.04/13.28      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 13.04/13.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.04/13.28        | ~ (l1_pre_topc @ sk_A))),
% 13.04/13.28      inference('sup-', [status(thm)], ['7', '8'])).
% 13.04/13.28  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('11', plain,
% 13.04/13.28      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 13.04/13.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('demod', [status(thm)], ['9', '10'])).
% 13.04/13.28  thf('12', plain,
% 13.04/13.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('13', plain,
% 13.04/13.28      (![X13 : $i, X14 : $i]:
% 13.04/13.28         (~ (l1_pre_topc @ X13)
% 13.04/13.28          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 13.04/13.28          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 13.04/13.28             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 13.04/13.28      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 13.04/13.28  thf('14', plain,
% 13.04/13.28      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 13.04/13.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.04/13.28        | ~ (l1_pre_topc @ sk_A))),
% 13.04/13.28      inference('sup-', [status(thm)], ['12', '13'])).
% 13.04/13.28  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('16', plain,
% 13.04/13.28      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 13.04/13.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('demod', [status(thm)], ['14', '15'])).
% 13.04/13.28  thf('17', plain,
% 13.04/13.28      (![X7 : $i, X8 : $i, X9 : $i]:
% 13.04/13.28         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 13.04/13.28          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 13.04/13.28          | ((k4_subset_1 @ X8 @ X7 @ X9) = (k2_xboole_0 @ X7 @ X9)))),
% 13.04/13.28      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 13.04/13.28  thf('18', plain,
% 13.04/13.28      (![X0 : $i]:
% 13.04/13.28         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 13.04/13.28            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 13.04/13.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 13.04/13.28      inference('sup-', [status(thm)], ['16', '17'])).
% 13.04/13.28  thf('19', plain,
% 13.04/13.28      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 13.04/13.28         (k1_tops_1 @ sk_A @ sk_C))
% 13.04/13.28         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 13.04/13.28      inference('sup-', [status(thm)], ['11', '18'])).
% 13.04/13.28  thf('20', plain,
% 13.04/13.28      (~ (r1_tarski @ 
% 13.04/13.28          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 13.04/13.28          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 13.04/13.28      inference('demod', [status(thm)], ['6', '19'])).
% 13.04/13.28  thf('21', plain,
% 13.04/13.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf(t3_subset, axiom,
% 13.04/13.28    (![A:$i,B:$i]:
% 13.04/13.28     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 13.04/13.28  thf('22', plain,
% 13.04/13.28      (![X10 : $i, X11 : $i]:
% 13.04/13.28         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 13.04/13.28      inference('cnf', [status(esa)], [t3_subset])).
% 13.04/13.28  thf('23', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 13.04/13.28      inference('sup-', [status(thm)], ['21', '22'])).
% 13.04/13.28  thf('24', plain,
% 13.04/13.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('25', plain,
% 13.04/13.28      (![X10 : $i, X11 : $i]:
% 13.04/13.28         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 13.04/13.28      inference('cnf', [status(esa)], [t3_subset])).
% 13.04/13.28  thf('26', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 13.04/13.28      inference('sup-', [status(thm)], ['24', '25'])).
% 13.04/13.28  thf(t8_xboole_1, axiom,
% 13.04/13.28    (![A:$i,B:$i,C:$i]:
% 13.04/13.28     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 13.04/13.28       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 13.04/13.28  thf('27', plain,
% 13.04/13.28      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.04/13.28         (~ (r1_tarski @ X4 @ X5)
% 13.04/13.28          | ~ (r1_tarski @ X6 @ X5)
% 13.04/13.28          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 13.04/13.28      inference('cnf', [status(esa)], [t8_xboole_1])).
% 13.04/13.28  thf('28', plain,
% 13.04/13.28      (![X0 : $i]:
% 13.04/13.28         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))
% 13.04/13.28          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('sup-', [status(thm)], ['26', '27'])).
% 13.04/13.28  thf('29', plain,
% 13.04/13.28      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (u1_struct_0 @ sk_A))),
% 13.04/13.28      inference('sup-', [status(thm)], ['23', '28'])).
% 13.04/13.28  thf('30', plain,
% 13.04/13.28      (![X10 : $i, X12 : $i]:
% 13.04/13.28         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 13.04/13.28      inference('cnf', [status(esa)], [t3_subset])).
% 13.04/13.28  thf('31', plain,
% 13.04/13.28      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 13.04/13.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('sup-', [status(thm)], ['29', '30'])).
% 13.04/13.28  thf('32', plain,
% 13.04/13.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf(t48_tops_1, axiom,
% 13.04/13.28    (![A:$i]:
% 13.04/13.28     ( ( l1_pre_topc @ A ) =>
% 13.04/13.28       ( ![B:$i]:
% 13.04/13.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.04/13.28           ( ![C:$i]:
% 13.04/13.28             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.04/13.28               ( ( r1_tarski @ B @ C ) =>
% 13.04/13.28                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 13.04/13.28  thf('33', plain,
% 13.04/13.28      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.04/13.28         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 13.04/13.28          | ~ (r1_tarski @ X15 @ X17)
% 13.04/13.28          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ (k1_tops_1 @ X16 @ X17))
% 13.04/13.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 13.04/13.28          | ~ (l1_pre_topc @ X16))),
% 13.04/13.28      inference('cnf', [status(esa)], [t48_tops_1])).
% 13.04/13.28  thf('34', plain,
% 13.04/13.28      (![X0 : $i]:
% 13.04/13.28         (~ (l1_pre_topc @ sk_A)
% 13.04/13.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.04/13.28          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 13.04/13.28          | ~ (r1_tarski @ sk_C @ X0))),
% 13.04/13.28      inference('sup-', [status(thm)], ['32', '33'])).
% 13.04/13.28  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('36', plain,
% 13.04/13.28      (![X0 : $i]:
% 13.04/13.28         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.04/13.28          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 13.04/13.28          | ~ (r1_tarski @ sk_C @ X0))),
% 13.04/13.28      inference('demod', [status(thm)], ['34', '35'])).
% 13.04/13.28  thf('37', plain,
% 13.04/13.28      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))
% 13.04/13.28        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 13.04/13.28           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 13.04/13.28      inference('sup-', [status(thm)], ['31', '36'])).
% 13.04/13.28  thf(commutativity_k2_xboole_0, axiom,
% 13.04/13.28    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 13.04/13.28  thf('38', plain,
% 13.04/13.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 13.04/13.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 13.04/13.28  thf(t7_xboole_1, axiom,
% 13.04/13.28    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 13.04/13.28  thf('39', plain,
% 13.04/13.28      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 13.04/13.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 13.04/13.28  thf('40', plain,
% 13.04/13.28      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 13.04/13.28      inference('sup+', [status(thm)], ['38', '39'])).
% 13.04/13.28  thf('41', plain,
% 13.04/13.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 13.04/13.28        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 13.04/13.28      inference('demod', [status(thm)], ['37', '40'])).
% 13.04/13.28  thf('42', plain,
% 13.04/13.28      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 13.04/13.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('sup-', [status(thm)], ['29', '30'])).
% 13.04/13.28  thf('43', plain,
% 13.04/13.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('44', plain,
% 13.04/13.28      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.04/13.28         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 13.04/13.28          | ~ (r1_tarski @ X15 @ X17)
% 13.04/13.28          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ (k1_tops_1 @ X16 @ X17))
% 13.04/13.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 13.04/13.28          | ~ (l1_pre_topc @ X16))),
% 13.04/13.28      inference('cnf', [status(esa)], [t48_tops_1])).
% 13.04/13.28  thf('45', plain,
% 13.04/13.28      (![X0 : $i]:
% 13.04/13.28         (~ (l1_pre_topc @ sk_A)
% 13.04/13.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.04/13.28          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 13.04/13.28          | ~ (r1_tarski @ sk_B @ X0))),
% 13.04/13.28      inference('sup-', [status(thm)], ['43', '44'])).
% 13.04/13.28  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 13.04/13.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.04/13.28  thf('47', plain,
% 13.04/13.28      (![X0 : $i]:
% 13.04/13.28         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.04/13.28          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 13.04/13.28          | ~ (r1_tarski @ sk_B @ X0))),
% 13.04/13.28      inference('demod', [status(thm)], ['45', '46'])).
% 13.04/13.28  thf('48', plain,
% 13.04/13.28      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 13.04/13.28        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 13.04/13.28           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 13.04/13.28      inference('sup-', [status(thm)], ['42', '47'])).
% 13.04/13.28  thf('49', plain,
% 13.04/13.28      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 13.04/13.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 13.04/13.28  thf('50', plain,
% 13.04/13.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 13.04/13.28        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 13.04/13.28      inference('demod', [status(thm)], ['48', '49'])).
% 13.04/13.28  thf('51', plain,
% 13.04/13.28      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.04/13.28         (~ (r1_tarski @ X4 @ X5)
% 13.04/13.28          | ~ (r1_tarski @ X6 @ X5)
% 13.04/13.28          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 13.04/13.28      inference('cnf', [status(esa)], [t8_xboole_1])).
% 13.04/13.28  thf('52', plain,
% 13.04/13.28      (![X0 : $i]:
% 13.04/13.28         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 13.04/13.28           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 13.04/13.28          | ~ (r1_tarski @ X0 @ 
% 13.04/13.28               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 13.04/13.28      inference('sup-', [status(thm)], ['50', '51'])).
% 13.04/13.28  thf('53', plain,
% 13.04/13.28      ((r1_tarski @ 
% 13.04/13.28        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 13.04/13.28        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 13.04/13.28      inference('sup-', [status(thm)], ['41', '52'])).
% 13.04/13.28  thf('54', plain, ($false), inference('demod', [status(thm)], ['20', '53'])).
% 13.04/13.28  
% 13.04/13.28  % SZS output end Refutation
% 13.04/13.28  
% 13.04/13.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
