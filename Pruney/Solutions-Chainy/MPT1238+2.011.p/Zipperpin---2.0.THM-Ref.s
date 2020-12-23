%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.10WcshAAdF

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:58 EST 2020

% Result     : Theorem 2.93s
% Output     : Refutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 128 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  671 (1956 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('46',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['20','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.10WcshAAdF
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:11:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.93/3.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.93/3.16  % Solved by: fo/fo7.sh
% 2.93/3.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.93/3.16  % done 1995 iterations in 2.706s
% 2.93/3.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.93/3.16  % SZS output start Refutation
% 2.93/3.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.93/3.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.93/3.16  thf(sk_A_type, type, sk_A: $i).
% 2.93/3.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.93/3.16  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.93/3.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.93/3.16  thf(sk_B_type, type, sk_B: $i).
% 2.93/3.16  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.93/3.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.93/3.16  thf(sk_C_type, type, sk_C: $i).
% 2.93/3.16  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.93/3.16  thf(t49_tops_1, conjecture,
% 2.93/3.16    (![A:$i]:
% 2.93/3.16     ( ( l1_pre_topc @ A ) =>
% 2.93/3.16       ( ![B:$i]:
% 2.93/3.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.16           ( ![C:$i]:
% 2.93/3.16             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.16               ( r1_tarski @
% 2.93/3.16                 ( k4_subset_1 @
% 2.93/3.16                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 2.93/3.16                   ( k1_tops_1 @ A @ C ) ) @ 
% 2.93/3.16                 ( k1_tops_1 @
% 2.93/3.16                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 2.93/3.16  thf(zf_stmt_0, negated_conjecture,
% 2.93/3.16    (~( ![A:$i]:
% 2.93/3.16        ( ( l1_pre_topc @ A ) =>
% 2.93/3.16          ( ![B:$i]:
% 2.93/3.16            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.16              ( ![C:$i]:
% 2.93/3.16                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.16                  ( r1_tarski @
% 2.93/3.16                    ( k4_subset_1 @
% 2.93/3.16                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 2.93/3.16                      ( k1_tops_1 @ A @ C ) ) @ 
% 2.93/3.16                    ( k1_tops_1 @
% 2.93/3.16                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 2.93/3.16    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 2.93/3.16  thf('0', plain,
% 2.93/3.16      (~ (r1_tarski @ 
% 2.93/3.16          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.93/3.16           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 2.93/3.16          (k1_tops_1 @ sk_A @ 
% 2.93/3.16           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('1', plain,
% 2.93/3.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('2', plain,
% 2.93/3.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf(redefinition_k4_subset_1, axiom,
% 2.93/3.16    (![A:$i,B:$i,C:$i]:
% 2.93/3.16     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.93/3.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.93/3.16       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.93/3.16  thf('3', plain,
% 2.93/3.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.93/3.16         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 2.93/3.16          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 2.93/3.16          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 2.93/3.16      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.93/3.16  thf('4', plain,
% 2.93/3.16      (![X0 : $i]:
% 2.93/3.16         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.93/3.16            = (k2_xboole_0 @ sk_B @ X0))
% 2.93/3.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.93/3.16      inference('sup-', [status(thm)], ['2', '3'])).
% 2.93/3.16  thf('5', plain,
% 2.93/3.16      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 2.93/3.16         = (k2_xboole_0 @ sk_B @ sk_C))),
% 2.93/3.16      inference('sup-', [status(thm)], ['1', '4'])).
% 2.93/3.16  thf('6', plain,
% 2.93/3.16      (~ (r1_tarski @ 
% 2.93/3.16          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.93/3.16           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 2.93/3.16          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.93/3.16      inference('demod', [status(thm)], ['0', '5'])).
% 2.93/3.16  thf('7', plain,
% 2.93/3.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf(dt_k1_tops_1, axiom,
% 2.93/3.16    (![A:$i,B:$i]:
% 2.93/3.16     ( ( ( l1_pre_topc @ A ) & 
% 2.93/3.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.93/3.16       ( m1_subset_1 @
% 2.93/3.16         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.93/3.16  thf('8', plain,
% 2.93/3.16      (![X13 : $i, X14 : $i]:
% 2.93/3.16         (~ (l1_pre_topc @ X13)
% 2.93/3.16          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.93/3.16          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 2.93/3.16             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 2.93/3.16      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.93/3.16  thf('9', plain,
% 2.93/3.16      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.93/3.16         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.93/3.16        | ~ (l1_pre_topc @ sk_A))),
% 2.93/3.16      inference('sup-', [status(thm)], ['7', '8'])).
% 2.93/3.16  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('11', plain,
% 2.93/3.16      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.93/3.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('demod', [status(thm)], ['9', '10'])).
% 2.93/3.16  thf('12', plain,
% 2.93/3.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('13', plain,
% 2.93/3.16      (![X13 : $i, X14 : $i]:
% 2.93/3.16         (~ (l1_pre_topc @ X13)
% 2.93/3.16          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.93/3.16          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 2.93/3.16             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 2.93/3.16      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.93/3.16  thf('14', plain,
% 2.93/3.16      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.93/3.16         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.93/3.16        | ~ (l1_pre_topc @ sk_A))),
% 2.93/3.16      inference('sup-', [status(thm)], ['12', '13'])).
% 2.93/3.16  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('16', plain,
% 2.93/3.16      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.93/3.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('demod', [status(thm)], ['14', '15'])).
% 2.93/3.16  thf('17', plain,
% 2.93/3.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.93/3.16         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 2.93/3.16          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 2.93/3.16          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 2.93/3.16      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.93/3.16  thf('18', plain,
% 2.93/3.16      (![X0 : $i]:
% 2.93/3.16         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.93/3.16            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 2.93/3.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.93/3.16      inference('sup-', [status(thm)], ['16', '17'])).
% 2.93/3.16  thf('19', plain,
% 2.93/3.16      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.93/3.16         (k1_tops_1 @ sk_A @ sk_C))
% 2.93/3.16         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 2.93/3.16      inference('sup-', [status(thm)], ['11', '18'])).
% 2.93/3.16  thf('20', plain,
% 2.93/3.16      (~ (r1_tarski @ 
% 2.93/3.16          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 2.93/3.16          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.93/3.16      inference('demod', [status(thm)], ['6', '19'])).
% 2.93/3.16  thf('21', plain,
% 2.93/3.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('22', plain,
% 2.93/3.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf(dt_k4_subset_1, axiom,
% 2.93/3.16    (![A:$i,B:$i,C:$i]:
% 2.93/3.16     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.93/3.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.93/3.16       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.93/3.16  thf('23', plain,
% 2.93/3.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.93/3.16         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.93/3.16          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 2.93/3.16          | (m1_subset_1 @ (k4_subset_1 @ X8 @ X7 @ X9) @ (k1_zfmisc_1 @ X8)))),
% 2.93/3.16      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 2.93/3.16  thf('24', plain,
% 2.93/3.16      (![X0 : $i]:
% 2.93/3.16         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 2.93/3.16           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.93/3.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.93/3.16      inference('sup-', [status(thm)], ['22', '23'])).
% 2.93/3.16  thf('25', plain,
% 2.93/3.16      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.93/3.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('sup-', [status(thm)], ['21', '24'])).
% 2.93/3.16  thf('26', plain,
% 2.93/3.16      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 2.93/3.16         = (k2_xboole_0 @ sk_B @ sk_C))),
% 2.93/3.16      inference('sup-', [status(thm)], ['1', '4'])).
% 2.93/3.16  thf('27', plain,
% 2.93/3.16      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 2.93/3.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('demod', [status(thm)], ['25', '26'])).
% 2.93/3.16  thf('28', plain,
% 2.93/3.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf(t48_tops_1, axiom,
% 2.93/3.16    (![A:$i]:
% 2.93/3.16     ( ( l1_pre_topc @ A ) =>
% 2.93/3.16       ( ![B:$i]:
% 2.93/3.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.16           ( ![C:$i]:
% 2.93/3.16             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.16               ( ( r1_tarski @ B @ C ) =>
% 2.93/3.16                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.93/3.16  thf('29', plain,
% 2.93/3.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.93/3.16         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 2.93/3.16          | ~ (r1_tarski @ X15 @ X17)
% 2.93/3.16          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ (k1_tops_1 @ X16 @ X17))
% 2.93/3.16          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 2.93/3.16          | ~ (l1_pre_topc @ X16))),
% 2.93/3.16      inference('cnf', [status(esa)], [t48_tops_1])).
% 2.93/3.16  thf('30', plain,
% 2.93/3.16      (![X0 : $i]:
% 2.93/3.16         (~ (l1_pre_topc @ sk_A)
% 2.93/3.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.93/3.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 2.93/3.16          | ~ (r1_tarski @ sk_C @ X0))),
% 2.93/3.16      inference('sup-', [status(thm)], ['28', '29'])).
% 2.93/3.16  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('32', plain,
% 2.93/3.16      (![X0 : $i]:
% 2.93/3.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.93/3.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 2.93/3.16          | ~ (r1_tarski @ sk_C @ X0))),
% 2.93/3.16      inference('demod', [status(thm)], ['30', '31'])).
% 2.93/3.16  thf('33', plain,
% 2.93/3.16      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.93/3.16        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.93/3.16           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.93/3.16      inference('sup-', [status(thm)], ['27', '32'])).
% 2.93/3.16  thf(commutativity_k2_xboole_0, axiom,
% 2.93/3.16    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.93/3.16  thf('34', plain,
% 2.93/3.16      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.93/3.16      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.93/3.16  thf(t7_xboole_1, axiom,
% 2.93/3.16    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.93/3.16  thf('35', plain,
% 2.93/3.16      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 2.93/3.16      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.93/3.16  thf('36', plain,
% 2.93/3.16      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.93/3.16      inference('sup+', [status(thm)], ['34', '35'])).
% 2.93/3.16  thf('37', plain,
% 2.93/3.16      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.93/3.16        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.93/3.16      inference('demod', [status(thm)], ['33', '36'])).
% 2.93/3.16  thf('38', plain,
% 2.93/3.16      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 2.93/3.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('demod', [status(thm)], ['25', '26'])).
% 2.93/3.16  thf('39', plain,
% 2.93/3.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('40', plain,
% 2.93/3.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.93/3.16         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 2.93/3.16          | ~ (r1_tarski @ X15 @ X17)
% 2.93/3.16          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ (k1_tops_1 @ X16 @ X17))
% 2.93/3.16          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 2.93/3.16          | ~ (l1_pre_topc @ X16))),
% 2.93/3.16      inference('cnf', [status(esa)], [t48_tops_1])).
% 2.93/3.16  thf('41', plain,
% 2.93/3.16      (![X0 : $i]:
% 2.93/3.16         (~ (l1_pre_topc @ sk_A)
% 2.93/3.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.93/3.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 2.93/3.16          | ~ (r1_tarski @ sk_B @ X0))),
% 2.93/3.16      inference('sup-', [status(thm)], ['39', '40'])).
% 2.93/3.16  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.16  thf('43', plain,
% 2.93/3.16      (![X0 : $i]:
% 2.93/3.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.93/3.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 2.93/3.16          | ~ (r1_tarski @ sk_B @ X0))),
% 2.93/3.16      inference('demod', [status(thm)], ['41', '42'])).
% 2.93/3.16  thf('44', plain,
% 2.93/3.16      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.93/3.16        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.93/3.16           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.93/3.16      inference('sup-', [status(thm)], ['38', '43'])).
% 2.93/3.16  thf('45', plain,
% 2.93/3.16      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 2.93/3.16      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.93/3.16  thf('46', plain,
% 2.93/3.16      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.93/3.16        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.93/3.16      inference('demod', [status(thm)], ['44', '45'])).
% 2.93/3.16  thf(t8_xboole_1, axiom,
% 2.93/3.16    (![A:$i,B:$i,C:$i]:
% 2.93/3.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.93/3.16       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.93/3.16  thf('47', plain,
% 2.93/3.16      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.93/3.16         (~ (r1_tarski @ X4 @ X5)
% 2.93/3.16          | ~ (r1_tarski @ X6 @ X5)
% 2.93/3.16          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 2.93/3.16      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.93/3.16  thf('48', plain,
% 2.93/3.16      (![X0 : $i]:
% 2.93/3.16         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 2.93/3.16           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 2.93/3.16          | ~ (r1_tarski @ X0 @ 
% 2.93/3.16               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 2.93/3.16      inference('sup-', [status(thm)], ['46', '47'])).
% 2.93/3.16  thf('49', plain,
% 2.93/3.16      ((r1_tarski @ 
% 2.93/3.16        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 2.93/3.16        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.93/3.16      inference('sup-', [status(thm)], ['37', '48'])).
% 2.93/3.16  thf('50', plain, ($false), inference('demod', [status(thm)], ['20', '49'])).
% 2.93/3.16  
% 2.93/3.16  % SZS output end Refutation
% 2.93/3.16  
% 2.93/3.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
