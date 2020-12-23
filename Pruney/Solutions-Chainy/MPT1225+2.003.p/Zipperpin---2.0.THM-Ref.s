%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sRtwZj8Lw0

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:46 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 470 expanded)
%              Number of leaves         :   21 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          : 1081 (8188 expanded)
%              Number of equality atoms :   61 ( 350 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t34_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                    = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X14 @ ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ X15 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_pre_topc @ X14 @ X13 ) @ ( k2_pre_topc @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','11','17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('37',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['20','29','35','36'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('41',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( k3_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','54'])).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf('70',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['40','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ X11 @ ( k2_pre_topc @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['70','71','78'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['39','79'])).

thf('81',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('83',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('85',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('87',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('88',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('91',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['80','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sRtwZj8Lw0
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.05/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.25  % Solved by: fo/fo7.sh
% 1.05/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.25  % done 700 iterations in 0.788s
% 1.05/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.25  % SZS output start Refutation
% 1.05/1.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.05/1.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.25  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.05/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.25  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.05/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.05/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.25  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.05/1.25  thf(t34_tops_1, conjecture,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( l1_pre_topc @ A ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ![C:$i]:
% 1.05/1.25             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 1.05/1.25                 ( ( k2_pre_topc @
% 1.05/1.25                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 1.05/1.25                   ( k9_subset_1 @
% 1.05/1.25                     ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.05/1.25                     ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 1.05/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.25    (~( ![A:$i]:
% 1.05/1.25        ( ( l1_pre_topc @ A ) =>
% 1.05/1.25          ( ![B:$i]:
% 1.05/1.25            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25              ( ![C:$i]:
% 1.05/1.25                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 1.05/1.25                    ( ( k2_pre_topc @
% 1.05/1.25                        A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 1.05/1.25                      ( k9_subset_1 @
% 1.05/1.25                        ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.05/1.25                        ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 1.05/1.25    inference('cnf.neg', [status(esa)], [t34_tops_1])).
% 1.05/1.25  thf('0', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('1', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(t51_pre_topc, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( l1_pre_topc @ A ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ![C:$i]:
% 1.05/1.25             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25               ( r1_tarski @
% 1.05/1.25                 ( k2_pre_topc @
% 1.05/1.25                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 1.05/1.25                 ( k9_subset_1 @
% 1.05/1.25                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.05/1.25                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 1.05/1.25  thf('2', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.05/1.25          | (r1_tarski @ 
% 1.05/1.25             (k2_pre_topc @ X14 @ 
% 1.05/1.25              (k9_subset_1 @ (u1_struct_0 @ X14) @ X13 @ X15)) @ 
% 1.05/1.25             (k9_subset_1 @ (u1_struct_0 @ X14) @ (k2_pre_topc @ X14 @ X13) @ 
% 1.05/1.25              (k2_pre_topc @ X14 @ X15)))
% 1.05/1.25          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.05/1.25          | ~ (l1_pre_topc @ X14))),
% 1.05/1.25      inference('cnf', [status(esa)], [t51_pre_topc])).
% 1.05/1.25  thf('3', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (~ (l1_pre_topc @ sk_A)
% 1.05/1.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.25          | (r1_tarski @ 
% 1.05/1.25             (k2_pre_topc @ sk_A @ 
% 1.05/1.25              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 1.05/1.25             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.25  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('5', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(commutativity_k9_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.25       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 1.05/1.25  thf('6', plain,
% 1.05/1.25      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 1.05/1.25          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 1.05/1.25      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 1.05/1.25  thf('7', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.05/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.25  thf('8', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(redefinition_k9_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.25       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.05/1.25  thf('9', plain,
% 1.05/1.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 1.05/1.25          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.05/1.25  thf('10', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.05/1.25           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.05/1.25      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.25  thf('11', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k3_xboole_0 @ X0 @ sk_B)
% 1.05/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.05/1.25      inference('demod', [status(thm)], ['7', '10'])).
% 1.05/1.25  thf('12', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(t52_pre_topc, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( l1_pre_topc @ A ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.05/1.25             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.05/1.25               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.05/1.25  thf('13', plain,
% 1.05/1.25      (![X16 : $i, X17 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.05/1.25          | ~ (v4_pre_topc @ X16 @ X17)
% 1.05/1.25          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 1.05/1.25          | ~ (l1_pre_topc @ X17))),
% 1.05/1.25      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.05/1.25  thf('14', plain,
% 1.05/1.25      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.25        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.05/1.25        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['12', '13'])).
% 1.05/1.25  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('16', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('17', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.05/1.25  thf('18', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k3_xboole_0 @ X0 @ sk_B)
% 1.05/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.05/1.25      inference('demod', [status(thm)], ['7', '10'])).
% 1.05/1.25  thf('19', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.25          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 1.05/1.25             (k3_xboole_0 @ (k2_pre_topc @ sk_A @ X0) @ sk_B)))),
% 1.05/1.25      inference('demod', [status(thm)], ['3', '4', '11', '17', '18'])).
% 1.05/1.25  thf('20', plain,
% 1.05/1.25      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)) @ 
% 1.05/1.25        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ sk_B))),
% 1.05/1.25      inference('sup-', [status(thm)], ['0', '19'])).
% 1.05/1.25  thf('21', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.05/1.25           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.05/1.25      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.25  thf('22', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('23', plain,
% 1.05/1.25      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 1.05/1.25          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 1.05/1.25      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 1.05/1.25  thf('24', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.05/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['22', '23'])).
% 1.05/1.25  thf('25', plain,
% 1.05/1.25      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 1.05/1.25         = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('sup+', [status(thm)], ['21', '24'])).
% 1.05/1.25  thf('26', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('27', plain,
% 1.05/1.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 1.05/1.25          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.05/1.25  thf('28', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.05/1.25           = (k3_xboole_0 @ X0 @ sk_C))),
% 1.05/1.25      inference('sup-', [status(thm)], ['26', '27'])).
% 1.05/1.25  thf('29', plain,
% 1.05/1.25      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['25', '28'])).
% 1.05/1.25  thf('30', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('31', plain,
% 1.05/1.25      (![X16 : $i, X17 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.05/1.25          | ~ (v4_pre_topc @ X16 @ X17)
% 1.05/1.25          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 1.05/1.25          | ~ (l1_pre_topc @ X17))),
% 1.05/1.25      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.05/1.25  thf('32', plain,
% 1.05/1.25      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.25        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C))
% 1.05/1.25        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['30', '31'])).
% 1.05/1.25  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('34', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('35', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 1.05/1.25      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.05/1.25  thf('36', plain,
% 1.05/1.25      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['25', '28'])).
% 1.05/1.25  thf('37', plain,
% 1.05/1.25      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.25        (k3_xboole_0 @ sk_B @ sk_C))),
% 1.05/1.25      inference('demod', [status(thm)], ['20', '29', '35', '36'])).
% 1.05/1.25  thf(t28_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.05/1.25  thf('38', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 1.05/1.25      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.25  thf('39', plain,
% 1.05/1.25      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.25         (k3_xboole_0 @ sk_B @ sk_C))
% 1.05/1.25         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['37', '38'])).
% 1.05/1.25  thf('40', plain,
% 1.05/1.25      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['25', '28'])).
% 1.05/1.25  thf('41', plain,
% 1.05/1.25      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.25         (k3_xboole_0 @ sk_B @ sk_C))
% 1.05/1.25         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['37', '38'])).
% 1.05/1.25  thf('42', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(dt_k9_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.25       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.05/1.25  thf('43', plain,
% 1.05/1.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.05/1.25         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 1.05/1.25          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.05/1.25  thf('44', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['42', '43'])).
% 1.05/1.25  thf('45', plain,
% 1.05/1.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.05/1.25         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 1.05/1.25          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.05/1.25  thf('46', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (m1_subset_1 @ 
% 1.05/1.25          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 1.05/1.25           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['44', '45'])).
% 1.05/1.25  thf('47', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.05/1.25           = (k3_xboole_0 @ X0 @ sk_C))),
% 1.05/1.25      inference('sup-', [status(thm)], ['26', '27'])).
% 1.05/1.25  thf('48', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (m1_subset_1 @ 
% 1.05/1.25          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['46', '47'])).
% 1.05/1.25  thf('49', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['42', '43'])).
% 1.05/1.25  thf('50', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.05/1.25           = (k3_xboole_0 @ X0 @ sk_C))),
% 1.05/1.25      inference('sup-', [status(thm)], ['26', '27'])).
% 1.05/1.25  thf('51', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.25  thf('52', plain,
% 1.05/1.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 1.05/1.25          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.05/1.25  thf('53', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ (k3_xboole_0 @ X0 @ sk_C))
% 1.05/1.25           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_C)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['51', '52'])).
% 1.05/1.25  thf('54', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['48', '53'])).
% 1.05/1.25  thf('55', plain,
% 1.05/1.25      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['41', '54'])).
% 1.05/1.25  thf('56', plain,
% 1.05/1.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 1.05/1.25          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.05/1.25  thf('57', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.05/1.25           (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.05/1.25           = (k3_xboole_0 @ X0 @ 
% 1.05/1.25              (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['55', '56'])).
% 1.05/1.25  thf('58', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('59', plain,
% 1.05/1.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.05/1.25         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 1.05/1.25          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.05/1.25  thf('60', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['58', '59'])).
% 1.05/1.25  thf('61', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.05/1.25           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.05/1.25      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.25  thf('62', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['60', '61'])).
% 1.05/1.25  thf('63', plain,
% 1.05/1.25      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 1.05/1.25          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 1.05/1.25      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 1.05/1.25  thf('64', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ (k3_xboole_0 @ X0 @ sk_B))
% 1.05/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.05/1.25              X1))),
% 1.05/1.25      inference('sup-', [status(thm)], ['62', '63'])).
% 1.05/1.25  thf('65', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['60', '61'])).
% 1.05/1.25  thf('66', plain,
% 1.05/1.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 1.05/1.25          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.05/1.25  thf('67', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ (k3_xboole_0 @ X0 @ sk_B))
% 1.05/1.25           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['65', '66'])).
% 1.05/1.25  thf('68', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_B))
% 1.05/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.05/1.25              X1))),
% 1.05/1.25      inference('demod', [status(thm)], ['64', '67'])).
% 1.05/1.25  thf('69', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.25           (k3_xboole_0 @ X0 @ sk_B))
% 1.05/1.25           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.05/1.25              (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['57', '68'])).
% 1.05/1.25  thf('70', plain,
% 1.05/1.25      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.25         (k3_xboole_0 @ sk_B @ sk_C))
% 1.05/1.25         = (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_B) @ 
% 1.05/1.25            (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['40', '69'])).
% 1.05/1.25  thf('71', plain,
% 1.05/1.25      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['25', '28'])).
% 1.05/1.25  thf('72', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 1.05/1.25          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.25  thf(t48_pre_topc, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( l1_pre_topc @ A ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 1.05/1.25  thf('73', plain,
% 1.05/1.25      (![X11 : $i, X12 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.05/1.25          | (r1_tarski @ X11 @ (k2_pre_topc @ X12 @ X11))
% 1.05/1.25          | ~ (l1_pre_topc @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [t48_pre_topc])).
% 1.05/1.25  thf('74', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (~ (l1_pre_topc @ sk_A)
% 1.05/1.25          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 1.05/1.25             (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['72', '73'])).
% 1.05/1.25  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('76', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 1.05/1.25          (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)))),
% 1.05/1.25      inference('demod', [status(thm)], ['74', '75'])).
% 1.05/1.25  thf('77', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 1.05/1.25      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.25  thf('78', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 1.05/1.25           (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)))
% 1.05/1.25           = (k3_xboole_0 @ X0 @ sk_C))),
% 1.05/1.25      inference('sup-', [status(thm)], ['76', '77'])).
% 1.05/1.25  thf('79', plain,
% 1.05/1.25      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.25         (k3_xboole_0 @ sk_B @ sk_C)) = (k3_xboole_0 @ sk_B @ sk_C))),
% 1.05/1.25      inference('demod', [status(thm)], ['70', '71', '78'])).
% 1.05/1.25  thf('80', plain,
% 1.05/1.25      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.05/1.25         = (k3_xboole_0 @ sk_B @ sk_C))),
% 1.05/1.25      inference('sup+', [status(thm)], ['39', '79'])).
% 1.05/1.25  thf('81', plain,
% 1.05/1.25      (((k2_pre_topc @ sk_A @ 
% 1.05/1.25         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 1.05/1.25         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25             (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_C)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('82', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.05/1.25  thf('83', plain,
% 1.05/1.25      (((k2_pre_topc @ sk_A @ 
% 1.05/1.25         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 1.05/1.25         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25             (k2_pre_topc @ sk_A @ sk_C)))),
% 1.05/1.25      inference('demod', [status(thm)], ['81', '82'])).
% 1.05/1.25  thf('84', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 1.05/1.25      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.05/1.25  thf('85', plain,
% 1.05/1.25      (((k2_pre_topc @ sk_A @ 
% 1.05/1.25         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 1.05/1.25         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 1.05/1.25      inference('demod', [status(thm)], ['83', '84'])).
% 1.05/1.25  thf('86', plain,
% 1.05/1.25      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 1.05/1.25         = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('sup+', [status(thm)], ['21', '24'])).
% 1.05/1.25  thf('87', plain,
% 1.05/1.25      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 1.05/1.25         = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('sup+', [status(thm)], ['21', '24'])).
% 1.05/1.25  thf('88', plain,
% 1.05/1.25      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))
% 1.05/1.25         != (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.05/1.25  thf('89', plain,
% 1.05/1.25      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['25', '28'])).
% 1.05/1.25  thf('90', plain,
% 1.05/1.25      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['25', '28'])).
% 1.05/1.25  thf('91', plain,
% 1.05/1.25      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.05/1.25         != (k3_xboole_0 @ sk_B @ sk_C))),
% 1.05/1.25      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.05/1.25  thf('92', plain, ($false),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['80', '91'])).
% 1.05/1.25  
% 1.05/1.25  % SZS output end Refutation
% 1.05/1.25  
% 1.05/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
