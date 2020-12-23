%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o2EEm0sZMK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:49 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 401 expanded)
%              Number of leaves         :   27 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          : 1216 (6635 expanded)
%              Number of equality atoms :   51 ( 147 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t40_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ B @ A )
                 => ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('4',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X14 @ X12 )
        = ( k9_subset_1 @ X13 @ X14 @ ( k3_subset_1 @ X13 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('15',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['17','20','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('32',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','35','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['25','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X14 @ X12 )
        = ( k9_subset_1 @ X13 @ X14 @ ( k3_subset_1 @ X13 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('53',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('55',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['41','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['17','20','23'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['40','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) @ ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k2_pre_topc @ X22 @ X23 ) ) @ ( k2_pre_topc @ X22 @ ( k7_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) ) @ ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('75',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('80',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('84',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['78','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('88',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['73','86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['63','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o2EEm0sZMK
% 0.14/0.36  % Computer   : n018.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:11:57 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.66/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.93  % Solved by: fo/fo7.sh
% 0.66/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.93  % done 458 iterations in 0.448s
% 0.66/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.93  % SZS output start Refutation
% 0.66/0.93  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.66/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.93  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.66/0.93  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.66/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.93  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.66/0.93  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.66/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.93  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.66/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.66/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.93  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.66/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.93  thf(t40_tops_1, conjecture,
% 0.66/0.93    (![A:$i]:
% 0.66/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.93       ( ![B:$i]:
% 0.66/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.93           ( ![C:$i]:
% 0.66/0.93             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.93               ( ( v3_pre_topc @ B @ A ) =>
% 0.66/0.93                 ( r1_tarski @
% 0.66/0.93                   ( k9_subset_1 @
% 0.66/0.93                     ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) @ 
% 0.66/0.93                   ( k2_pre_topc @
% 0.66/0.93                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.66/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.93    (~( ![A:$i]:
% 0.66/0.93        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.93          ( ![B:$i]:
% 0.66/0.93            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.93              ( ![C:$i]:
% 0.66/0.93                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.93                  ( ( v3_pre_topc @ B @ A ) =>
% 0.66/0.93                    ( r1_tarski @
% 0.66/0.93                      ( k9_subset_1 @
% 0.66/0.93                        ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) @ 
% 0.66/0.93                      ( k2_pre_topc @
% 0.66/0.93                        A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ) )),
% 0.66/0.93    inference('cnf.neg', [status(esa)], [t40_tops_1])).
% 0.66/0.93  thf('0', plain,
% 0.66/0.93      (~ (r1_tarski @ 
% 0.66/0.93          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.93           (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.66/0.93          (k2_pre_topc @ sk_A @ 
% 0.66/0.93           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('1', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('2', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(dt_k3_subset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.93       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.66/0.93  thf('3', plain,
% 0.66/0.93      (![X5 : $i, X6 : $i]:
% 0.66/0.93         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 0.66/0.93          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.66/0.93      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.66/0.93  thf('4', plain,
% 0.66/0.93      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.66/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.66/0.93  thf('5', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(d5_subset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.93       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.66/0.93  thf('6', plain,
% 0.66/0.93      (![X3 : $i, X4 : $i]:
% 0.66/0.93         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.66/0.93          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.66/0.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.66/0.93  thf('7', plain,
% 0.66/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.66/0.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.66/0.93      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.93  thf('8', plain,
% 0.66/0.93      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.66/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('demod', [status(thm)], ['4', '7'])).
% 0.66/0.93  thf(t32_subset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.93       ( ![C:$i]:
% 0.66/0.93         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.93           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.66/0.93             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.66/0.93  thf('9', plain,
% 0.66/0.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.93         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.66/0.93          | ((k7_subset_1 @ X13 @ X14 @ X12)
% 0.66/0.93              = (k9_subset_1 @ X13 @ X14 @ (k3_subset_1 @ X13 @ X12)))
% 0.66/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.66/0.93      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.66/0.93  thf('10', plain,
% 0.66/0.93      (![X0 : $i]:
% 0.66/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.93          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.66/0.93              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.93              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.66/0.93                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.93                  (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.66/0.93  thf('11', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(involutiveness_k3_subset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.93       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.66/0.93  thf('12', plain,
% 0.66/0.93      (![X7 : $i, X8 : $i]:
% 0.66/0.93         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.66/0.93          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.66/0.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.66/0.93  thf('13', plain,
% 0.66/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.93         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.66/0.93      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.93  thf('14', plain,
% 0.66/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.66/0.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.66/0.93      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.93  thf('15', plain,
% 0.66/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.66/0.93      inference('demod', [status(thm)], ['13', '14'])).
% 0.66/0.93  thf('16', plain,
% 0.66/0.93      (![X0 : $i]:
% 0.66/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.93          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.66/0.93              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.93              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))),
% 0.66/0.93      inference('demod', [status(thm)], ['10', '15'])).
% 0.66/0.93  thf('17', plain,
% 0.66/0.93      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.66/0.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.93         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B))),
% 0.66/0.93      inference('sup-', [status(thm)], ['1', '16'])).
% 0.66/0.93  thf('18', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(redefinition_k7_subset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i,C:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.93       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.66/0.93  thf('19', plain,
% 0.66/0.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.66/0.93         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.66/0.93          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.66/0.93      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.66/0.93  thf('20', plain,
% 0.66/0.93      (![X0 : $i]:
% 0.66/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.66/0.93           = (k4_xboole_0 @ sk_C @ X0))),
% 0.66/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.66/0.93  thf('21', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(commutativity_k9_subset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i,C:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.93       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.66/0.93  thf('22', plain,
% 0.66/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.93         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 0.66/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.66/0.93      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.66/0.93  thf('23', plain,
% 0.66/0.93      (![X0 : $i]:
% 0.66/0.93         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.66/0.93           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.66/0.93      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.93  thf('24', plain,
% 0.66/0.93      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.93         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.66/0.93      inference('demod', [status(thm)], ['17', '20', '23'])).
% 0.66/0.93  thf('25', plain,
% 0.66/0.93      (~ (r1_tarski @ 
% 0.66/0.93          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.93           (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.66/0.93          (k2_pre_topc @ sk_A @ 
% 0.66/0.93           (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.66/0.93      inference('demod', [status(thm)], ['0', '24'])).
% 0.66/0.93  thf('26', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(dt_k2_pre_topc, axiom,
% 0.66/0.93    (![A:$i,B:$i]:
% 0.66/0.93     ( ( ( l1_pre_topc @ A ) & 
% 0.66/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.66/0.93       ( m1_subset_1 @
% 0.66/0.93         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.66/0.93  thf('27', plain,
% 0.66/0.93      (![X15 : $i, X16 : $i]:
% 0.66/0.93         (~ (l1_pre_topc @ X15)
% 0.66/0.93          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.66/0.93          | (m1_subset_1 @ (k2_pre_topc @ X15 @ X16) @ 
% 0.66/0.93             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.66/0.93      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.66/0.93  thf('28', plain,
% 0.66/0.93      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.66/0.93         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.93        | ~ (l1_pre_topc @ sk_A))),
% 0.66/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.93  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('30', plain,
% 0.66/0.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.66/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('demod', [status(thm)], ['28', '29'])).
% 0.66/0.93  thf('31', plain,
% 0.66/0.93      (![X0 : $i]:
% 0.66/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.93          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.66/0.93              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.93              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))),
% 0.66/0.93      inference('demod', [status(thm)], ['10', '15'])).
% 0.66/0.93  thf('32', plain,
% 0.66/0.93      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.66/0.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.93         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.66/0.93            sk_B))),
% 0.66/0.93      inference('sup-', [status(thm)], ['30', '31'])).
% 0.66/0.93  thf('33', plain,
% 0.66/0.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.66/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('demod', [status(thm)], ['28', '29'])).
% 0.66/0.93  thf('34', plain,
% 0.66/0.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.66/0.93         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.66/0.93          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.66/0.93      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.66/0.93  thf('35', plain,
% 0.66/0.93      (![X0 : $i]:
% 0.77/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ X0))),
% 0.77/0.93      inference('sup-', [status(thm)], ['33', '34'])).
% 0.77/0.93  thf('36', plain,
% 0.77/0.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('demod', [status(thm)], ['28', '29'])).
% 0.77/0.93  thf('37', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.93         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 0.77/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.77/0.93      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.77/0.93  thf('38', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.77/0.93           (k2_pre_topc @ sk_A @ sk_C))
% 0.77/0.93           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93              (k2_pre_topc @ sk_A @ sk_C) @ X0))),
% 0.77/0.93      inference('sup-', [status(thm)], ['36', '37'])).
% 0.77/0.93  thf('39', plain,
% 0.77/0.93      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.77/0.93         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.93            (k2_pre_topc @ sk_A @ sk_C)))),
% 0.77/0.93      inference('demod', [status(thm)], ['32', '35', '38'])).
% 0.77/0.93  thf('40', plain,
% 0.77/0.93      (~ (r1_tarski @ 
% 0.77/0.93          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.77/0.93          (k2_pre_topc @ sk_A @ 
% 0.77/0.93           (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.77/0.93      inference('demod', [status(thm)], ['25', '39'])).
% 0.77/0.93  thf('41', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('42', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('43', plain,
% 0.77/0.93      (![X5 : $i, X6 : $i]:
% 0.77/0.93         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 0.77/0.93          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.77/0.93      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.77/0.93  thf('44', plain,
% 0.77/0.93      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.77/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['42', '43'])).
% 0.77/0.93  thf('45', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('46', plain,
% 0.77/0.93      (![X3 : $i, X4 : $i]:
% 0.77/0.93         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.77/0.93          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.77/0.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.77/0.93  thf('47', plain,
% 0.77/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.77/0.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.77/0.93  thf('48', plain,
% 0.77/0.93      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.77/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('demod', [status(thm)], ['44', '47'])).
% 0.77/0.93  thf('49', plain,
% 0.77/0.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.77/0.93          | ((k7_subset_1 @ X13 @ X14 @ X12)
% 0.77/0.93              = (k9_subset_1 @ X13 @ X14 @ (k3_subset_1 @ X13 @ X12)))
% 0.77/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.77/0.93      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.77/0.93  thf('50', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.93          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.77/0.93              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.77/0.93              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.77/0.93                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                  (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/0.93  thf('51', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('52', plain,
% 0.77/0.93      (![X7 : $i, X8 : $i]:
% 0.77/0.93         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.77/0.93          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.77/0.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.77/0.93  thf('53', plain,
% 0.77/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['51', '52'])).
% 0.77/0.93  thf('54', plain,
% 0.77/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.77/0.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.77/0.93  thf('55', plain,
% 0.77/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.93  thf('56', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.93          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.77/0.93              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.77/0.93              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)))),
% 0.77/0.93      inference('demod', [status(thm)], ['50', '55'])).
% 0.77/0.93  thf('57', plain,
% 0.77/0.93      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.77/0.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.77/0.93         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['41', '56'])).
% 0.77/0.93  thf('58', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('59', plain,
% 0.77/0.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.77/0.93          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.77/0.93      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.77/0.93  thf('60', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.77/0.93           = (k4_xboole_0 @ sk_B @ X0))),
% 0.77/0.93      inference('sup-', [status(thm)], ['58', '59'])).
% 0.77/0.93  thf('61', plain,
% 0.77/0.93      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.77/0.93         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['17', '20', '23'])).
% 0.77/0.93  thf('62', plain,
% 0.77/0.93      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.77/0.93         = (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.77/0.93      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.77/0.93  thf('63', plain,
% 0.77/0.93      (~ (r1_tarski @ 
% 0.77/0.93          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.77/0.93          (k2_pre_topc @ sk_A @ 
% 0.77/0.93           (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.77/0.93      inference('demod', [status(thm)], ['40', '62'])).
% 0.77/0.93  thf('64', plain,
% 0.77/0.93      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.77/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('demod', [status(thm)], ['4', '7'])).
% 0.77/0.93  thf('65', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf(t32_tops_1, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.93       ( ![B:$i]:
% 0.77/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.93           ( ![C:$i]:
% 0.77/0.93             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.93               ( r1_tarski @
% 0.77/0.93                 ( k7_subset_1 @
% 0.77/0.93                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.77/0.93                   ( k2_pre_topc @ A @ C ) ) @ 
% 0.77/0.93                 ( k2_pre_topc @
% 0.77/0.93                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.77/0.93  thf('66', plain,
% 0.77/0.93      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.77/0.93          | (r1_tarski @ 
% 0.77/0.93             (k7_subset_1 @ (u1_struct_0 @ X22) @ (k2_pre_topc @ X22 @ X21) @ 
% 0.77/0.93              (k2_pre_topc @ X22 @ X23)) @ 
% 0.77/0.93             (k2_pre_topc @ X22 @ 
% 0.77/0.93              (k7_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X23)))
% 0.77/0.93          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.77/0.93          | ~ (l1_pre_topc @ X22)
% 0.77/0.93          | ~ (v2_pre_topc @ X22))),
% 0.77/0.93      inference('cnf', [status(esa)], [t32_tops_1])).
% 0.77/0.93  thf('67', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (v2_pre_topc @ sk_A)
% 0.77/0.93          | ~ (l1_pre_topc @ sk_A)
% 0.77/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.93          | (r1_tarski @ 
% 0.77/0.93             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93              (k2_pre_topc @ sk_A @ sk_C) @ (k2_pre_topc @ sk_A @ X0)) @ 
% 0.77/0.93             (k2_pre_topc @ sk_A @ 
% 0.77/0.93              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['65', '66'])).
% 0.77/0.93  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('70', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ X0))),
% 0.77/0.93      inference('sup-', [status(thm)], ['33', '34'])).
% 0.77/0.93  thf('71', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.77/0.93           = (k4_xboole_0 @ sk_C @ X0))),
% 0.77/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/0.93  thf('72', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.93          | (r1_tarski @ 
% 0.77/0.93             (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93              (k2_pre_topc @ sk_A @ X0)) @ 
% 0.77/0.93             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_C @ X0))))),
% 0.77/0.93      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.77/0.93  thf('73', plain,
% 0.77/0.93      ((r1_tarski @ 
% 0.77/0.93        (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.77/0.93        (k2_pre_topc @ sk_A @ 
% 0.77/0.93         (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['64', '72'])).
% 0.77/0.93  thf('74', plain,
% 0.77/0.93      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.77/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('demod', [status(thm)], ['4', '7'])).
% 0.77/0.93  thf(t52_pre_topc, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( l1_pre_topc @ A ) =>
% 0.77/0.93       ( ![B:$i]:
% 0.77/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.93           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.77/0.93             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.77/0.93               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.77/0.93  thf('75', plain,
% 0.77/0.93      (![X17 : $i, X18 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.77/0.93          | ~ (v4_pre_topc @ X17 @ X18)
% 0.77/0.93          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.77/0.93          | ~ (l1_pre_topc @ X18))),
% 0.77/0.93      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.77/0.93  thf('76', plain,
% 0.77/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.93        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.77/0.93            = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.77/0.93        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.77/0.93      inference('sup-', [status(thm)], ['74', '75'])).
% 0.77/0.93  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('78', plain,
% 0.77/0.93      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.77/0.93          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.77/0.93        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.77/0.93      inference('demod', [status(thm)], ['76', '77'])).
% 0.77/0.93  thf('79', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf(t30_tops_1, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( l1_pre_topc @ A ) =>
% 0.77/0.93       ( ![B:$i]:
% 0.77/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.93           ( ( v3_pre_topc @ B @ A ) <=>
% 0.77/0.93             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.77/0.93  thf('80', plain,
% 0.77/0.93      (![X19 : $i, X20 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.77/0.93          | ~ (v3_pre_topc @ X19 @ X20)
% 0.77/0.93          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.77/0.93          | ~ (l1_pre_topc @ X20))),
% 0.77/0.93      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.77/0.93  thf('81', plain,
% 0.77/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.93        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.77/0.93        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.77/0.93      inference('sup-', [status(thm)], ['79', '80'])).
% 0.77/0.93  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('83', plain,
% 0.77/0.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.77/0.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.77/0.93      inference('sup-', [status(thm)], ['5', '6'])).
% 0.77/0.93  thf('84', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('85', plain,
% 0.77/0.93      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.77/0.93      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.77/0.93  thf('86', plain,
% 0.77/0.93      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.77/0.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.77/0.93      inference('demod', [status(thm)], ['78', '85'])).
% 0.77/0.93  thf('87', plain,
% 0.77/0.93      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.77/0.93         = (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.77/0.93      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.77/0.93  thf('88', plain,
% 0.77/0.93      ((r1_tarski @ 
% 0.77/0.93        (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.77/0.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.77/0.93        (k2_pre_topc @ sk_A @ 
% 0.77/0.93         (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.77/0.93      inference('demod', [status(thm)], ['73', '86', '87'])).
% 0.77/0.93  thf('89', plain, ($false), inference('demod', [status(thm)], ['63', '88'])).
% 0.77/0.93  
% 0.77/0.93  % SZS output end Refutation
% 0.77/0.93  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
