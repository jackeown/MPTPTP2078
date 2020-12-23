%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jffrj0IDI2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:19 EST 2020

% Result     : Theorem 17.76s
% Output     : Refutation 17.76s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 334 expanded)
%              Number of leaves         :   20 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  997 (3133 expanded)
%              Number of equality atoms :   23 (  88 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t51_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_pre_topc])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_C @ ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( r1_tarski @ ( k2_pre_topc @ X22 @ X21 ) @ ( k2_pre_topc @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['32','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('72',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('74',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( r1_tarski @ ( k2_pre_topc @ X22 @ X21 ) @ ( k2_pre_topc @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('94',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['12','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jffrj0IDI2
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.76/17.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.76/17.95  % Solved by: fo/fo7.sh
% 17.76/17.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.76/17.95  % done 17865 iterations in 17.491s
% 17.76/17.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.76/17.95  % SZS output start Refutation
% 17.76/17.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.76/17.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.76/17.95  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 17.76/17.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.76/17.95  thf(sk_A_type, type, sk_A: $i).
% 17.76/17.95  thf(sk_C_type, type, sk_C: $i).
% 17.76/17.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 17.76/17.95  thf(sk_B_type, type, sk_B: $i).
% 17.76/17.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 17.76/17.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.76/17.95  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 17.76/17.95  thf(t51_pre_topc, conjecture,
% 17.76/17.95    (![A:$i]:
% 17.76/17.95     ( ( l1_pre_topc @ A ) =>
% 17.76/17.95       ( ![B:$i]:
% 17.76/17.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.76/17.95           ( ![C:$i]:
% 17.76/17.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.76/17.95               ( r1_tarski @
% 17.76/17.95                 ( k2_pre_topc @
% 17.76/17.95                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 17.76/17.95                 ( k9_subset_1 @
% 17.76/17.95                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 17.76/17.95                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 17.76/17.95  thf(zf_stmt_0, negated_conjecture,
% 17.76/17.95    (~( ![A:$i]:
% 17.76/17.95        ( ( l1_pre_topc @ A ) =>
% 17.76/17.95          ( ![B:$i]:
% 17.76/17.95            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.76/17.95              ( ![C:$i]:
% 17.76/17.95                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.76/17.95                  ( r1_tarski @
% 17.76/17.95                    ( k2_pre_topc @
% 17.76/17.95                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 17.76/17.95                    ( k9_subset_1 @
% 17.76/17.95                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 17.76/17.95                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 17.76/17.95    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 17.76/17.95  thf('0', plain,
% 17.76/17.95      (~ (r1_tarski @ 
% 17.76/17.95          (k2_pre_topc @ sk_A @ 
% 17.76/17.95           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 17.76/17.95          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.76/17.95           (k2_pre_topc @ sk_A @ sk_C)))),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('1', plain,
% 17.76/17.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf(redefinition_k9_subset_1, axiom,
% 17.76/17.95    (![A:$i,B:$i,C:$i]:
% 17.76/17.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 17.76/17.95       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 17.76/17.95  thf('2', plain,
% 17.76/17.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.76/17.95         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 17.76/17.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 17.76/17.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 17.76/17.95  thf('3', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 17.76/17.95           = (k3_xboole_0 @ X0 @ sk_C))),
% 17.76/17.95      inference('sup-', [status(thm)], ['1', '2'])).
% 17.76/17.95  thf('4', plain,
% 17.76/17.95      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 17.76/17.95          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.76/17.95           (k2_pre_topc @ sk_A @ sk_C)))),
% 17.76/17.95      inference('demod', [status(thm)], ['0', '3'])).
% 17.76/17.95  thf('5', plain,
% 17.76/17.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf(dt_k2_pre_topc, axiom,
% 17.76/17.95    (![A:$i,B:$i]:
% 17.76/17.95     ( ( ( l1_pre_topc @ A ) & 
% 17.76/17.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.76/17.95       ( m1_subset_1 @
% 17.76/17.95         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 17.76/17.95  thf('6', plain,
% 17.76/17.95      (![X19 : $i, X20 : $i]:
% 17.76/17.95         (~ (l1_pre_topc @ X19)
% 17.76/17.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 17.76/17.95          | (m1_subset_1 @ (k2_pre_topc @ X19 @ X20) @ 
% 17.76/17.95             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 17.76/17.95      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 17.76/17.95  thf('7', plain,
% 17.76/17.95      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 17.76/17.95         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.76/17.95        | ~ (l1_pre_topc @ sk_A))),
% 17.76/17.95      inference('sup-', [status(thm)], ['5', '6'])).
% 17.76/17.95  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('9', plain,
% 17.76/17.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 17.76/17.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('demod', [status(thm)], ['7', '8'])).
% 17.76/17.95  thf('10', plain,
% 17.76/17.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.76/17.95         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 17.76/17.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 17.76/17.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 17.76/17.95  thf('11', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 17.76/17.95           (k2_pre_topc @ sk_A @ sk_C))
% 17.76/17.95           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['9', '10'])).
% 17.76/17.95  thf('12', plain,
% 17.76/17.95      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 17.76/17.95          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.76/17.95           (k2_pre_topc @ sk_A @ sk_C)))),
% 17.76/17.95      inference('demod', [status(thm)], ['4', '11'])).
% 17.76/17.95  thf(t17_xboole_1, axiom,
% 17.76/17.95    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 17.76/17.95  thf('13', plain,
% 17.76/17.95      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 17.76/17.95      inference('cnf', [status(esa)], [t17_xboole_1])).
% 17.76/17.95  thf(d10_xboole_0, axiom,
% 17.76/17.95    (![A:$i,B:$i]:
% 17.76/17.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 17.76/17.95  thf('14', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 17.76/17.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.76/17.95  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.76/17.95      inference('simplify', [status(thm)], ['14'])).
% 17.76/17.95  thf(t3_subset, axiom,
% 17.76/17.95    (![A:$i,B:$i]:
% 17.76/17.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.76/17.95  thf('16', plain,
% 17.76/17.95      (![X16 : $i, X18 : $i]:
% 17.76/17.95         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 17.76/17.95      inference('cnf', [status(esa)], [t3_subset])).
% 17.76/17.95  thf('17', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['15', '16'])).
% 17.76/17.95  thf(dt_k9_subset_1, axiom,
% 17.76/17.95    (![A:$i,B:$i,C:$i]:
% 17.76/17.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 17.76/17.95       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 17.76/17.95  thf('18', plain,
% 17.76/17.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 17.76/17.95         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 17.76/17.95          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 17.76/17.95      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 17.76/17.95  thf('19', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['17', '18'])).
% 17.76/17.95  thf('20', plain,
% 17.76/17.95      (![X16 : $i, X17 : $i]:
% 17.76/17.95         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 17.76/17.95      inference('cnf', [status(esa)], [t3_subset])).
% 17.76/17.95  thf('21', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 17.76/17.95      inference('sup-', [status(thm)], ['19', '20'])).
% 17.76/17.95  thf('22', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['15', '16'])).
% 17.76/17.95  thf('23', plain,
% 17.76/17.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.76/17.95         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 17.76/17.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 17.76/17.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 17.76/17.95  thf('24', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['22', '23'])).
% 17.76/17.95  thf('25', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.76/17.95      inference('demod', [status(thm)], ['21', '24'])).
% 17.76/17.95  thf(t19_xboole_1, axiom,
% 17.76/17.95    (![A:$i,B:$i,C:$i]:
% 17.76/17.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 17.76/17.95       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 17.76/17.95  thf('26', plain,
% 17.76/17.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.76/17.95         (~ (r1_tarski @ X5 @ X6)
% 17.76/17.95          | ~ (r1_tarski @ X5 @ X7)
% 17.76/17.95          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.76/17.95      inference('cnf', [status(esa)], [t19_xboole_1])).
% 17.76/17.95  thf('27', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.76/17.95         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))
% 17.76/17.95          | ~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 17.76/17.95      inference('sup-', [status(thm)], ['25', '26'])).
% 17.76/17.95  thf('28', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['13', '27'])).
% 17.76/17.95  thf('29', plain,
% 17.76/17.95      (![X0 : $i, X2 : $i]:
% 17.76/17.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 17.76/17.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.76/17.95  thf('30', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 17.76/17.95          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['28', '29'])).
% 17.76/17.95  thf('31', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['13', '27'])).
% 17.76/17.95  thf('32', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.76/17.95      inference('demod', [status(thm)], ['30', '31'])).
% 17.76/17.95  thf('33', plain,
% 17.76/17.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('34', plain,
% 17.76/17.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('35', plain,
% 17.76/17.95      (![X16 : $i, X17 : $i]:
% 17.76/17.95         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 17.76/17.95      inference('cnf', [status(esa)], [t3_subset])).
% 17.76/17.95  thf('36', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 17.76/17.95      inference('sup-', [status(thm)], ['34', '35'])).
% 17.76/17.95  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.76/17.95      inference('simplify', [status(thm)], ['14'])).
% 17.76/17.95  thf('38', plain,
% 17.76/17.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.76/17.95         (~ (r1_tarski @ X5 @ X6)
% 17.76/17.95          | ~ (r1_tarski @ X5 @ X7)
% 17.76/17.95          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.76/17.95      inference('cnf', [status(esa)], [t19_xboole_1])).
% 17.76/17.95  thf('39', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 17.76/17.95      inference('sup-', [status(thm)], ['37', '38'])).
% 17.76/17.95  thf('40', plain,
% 17.76/17.95      ((r1_tarski @ sk_C @ (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['36', '39'])).
% 17.76/17.95  thf('41', plain,
% 17.76/17.95      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 17.76/17.95      inference('cnf', [status(esa)], [t17_xboole_1])).
% 17.76/17.95  thf('42', plain,
% 17.76/17.95      (![X0 : $i, X2 : $i]:
% 17.76/17.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 17.76/17.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.76/17.95  thf('43', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 17.76/17.95          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['41', '42'])).
% 17.76/17.95  thf('44', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['40', '43'])).
% 17.76/17.95  thf('45', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['17', '18'])).
% 17.76/17.95  thf('46', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['22', '23'])).
% 17.76/17.95  thf('47', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 17.76/17.95      inference('demod', [status(thm)], ['45', '46'])).
% 17.76/17.95  thf('48', plain,
% 17.76/17.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 17.76/17.95         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 17.76/17.95          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 17.76/17.95      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 17.76/17.95  thf('49', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k9_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 17.76/17.95          (k1_zfmisc_1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['47', '48'])).
% 17.76/17.95  thf('50', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 17.76/17.95          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('sup+', [status(thm)], ['44', '49'])).
% 17.76/17.95  thf('51', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 17.76/17.95           = (k3_xboole_0 @ X0 @ sk_C))),
% 17.76/17.95      inference('sup-', [status(thm)], ['1', '2'])).
% 17.76/17.95  thf('52', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 17.76/17.95          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('demod', [status(thm)], ['50', '51'])).
% 17.76/17.95  thf(t49_pre_topc, axiom,
% 17.76/17.95    (![A:$i]:
% 17.76/17.95     ( ( l1_pre_topc @ A ) =>
% 17.76/17.95       ( ![B:$i]:
% 17.76/17.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.76/17.95           ( ![C:$i]:
% 17.76/17.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.76/17.95               ( ( r1_tarski @ B @ C ) =>
% 17.76/17.95                 ( r1_tarski @
% 17.76/17.95                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 17.76/17.95  thf('53', plain,
% 17.76/17.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 17.76/17.95         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 17.76/17.95          | ~ (r1_tarski @ X21 @ X23)
% 17.76/17.95          | (r1_tarski @ (k2_pre_topc @ X22 @ X21) @ (k2_pre_topc @ X22 @ X23))
% 17.76/17.95          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 17.76/17.95          | ~ (l1_pre_topc @ X22))),
% 17.76/17.95      inference('cnf', [status(esa)], [t49_pre_topc])).
% 17.76/17.95  thf('54', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (~ (l1_pre_topc @ sk_A)
% 17.76/17.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.76/17.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 17.76/17.95             (k2_pre_topc @ sk_A @ X1))
% 17.76/17.95          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 17.76/17.95      inference('sup-', [status(thm)], ['52', '53'])).
% 17.76/17.95  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('56', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.76/17.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 17.76/17.95             (k2_pre_topc @ sk_A @ X1))
% 17.76/17.95          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 17.76/17.95      inference('demod', [status(thm)], ['54', '55'])).
% 17.76/17.95  thf('57', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 17.76/17.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 17.76/17.95             (k2_pre_topc @ sk_A @ sk_C)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['33', '56'])).
% 17.76/17.95  thf('58', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.76/17.95      inference('demod', [status(thm)], ['21', '24'])).
% 17.76/17.95  thf('59', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 17.76/17.95          (k2_pre_topc @ sk_A @ sk_C))),
% 17.76/17.95      inference('demod', [status(thm)], ['57', '58'])).
% 17.76/17.95  thf('60', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 17.76/17.95          (k2_pre_topc @ sk_A @ sk_C))),
% 17.76/17.95      inference('sup+', [status(thm)], ['32', '59'])).
% 17.76/17.95  thf('61', plain,
% 17.76/17.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('62', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.76/17.95      inference('simplify', [status(thm)], ['14'])).
% 17.76/17.95  thf('63', plain,
% 17.76/17.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('64', plain,
% 17.76/17.95      (![X16 : $i, X17 : $i]:
% 17.76/17.95         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 17.76/17.95      inference('cnf', [status(esa)], [t3_subset])).
% 17.76/17.95  thf('65', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.76/17.95      inference('sup-', [status(thm)], ['63', '64'])).
% 17.76/17.95  thf('66', plain,
% 17.76/17.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.76/17.95         (~ (r1_tarski @ X5 @ X6)
% 17.76/17.95          | ~ (r1_tarski @ X5 @ X7)
% 17.76/17.95          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.76/17.95      inference('cnf', [status(esa)], [t19_xboole_1])).
% 17.76/17.95  thf('67', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         ((r1_tarski @ sk_B @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 17.76/17.95          | ~ (r1_tarski @ sk_B @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['65', '66'])).
% 17.76/17.95  thf('68', plain,
% 17.76/17.95      ((r1_tarski @ sk_B @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 17.76/17.95      inference('sup-', [status(thm)], ['62', '67'])).
% 17.76/17.95  thf('69', plain,
% 17.76/17.95      (![X0 : $i, X2 : $i]:
% 17.76/17.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 17.76/17.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.76/17.95  thf('70', plain,
% 17.76/17.95      ((~ (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 17.76/17.95        | ((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (sk_B)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['68', '69'])).
% 17.76/17.95  thf('71', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.76/17.95      inference('demod', [status(thm)], ['21', '24'])).
% 17.76/17.95  thf('72', plain, (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 17.76/17.95      inference('demod', [status(thm)], ['70', '71'])).
% 17.76/17.95  thf('73', plain,
% 17.76/17.95      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 17.76/17.95      inference('cnf', [status(esa)], [t17_xboole_1])).
% 17.76/17.95  thf('74', plain,
% 17.76/17.95      (![X16 : $i, X18 : $i]:
% 17.76/17.95         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 17.76/17.95      inference('cnf', [status(esa)], [t3_subset])).
% 17.76/17.95  thf('75', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['73', '74'])).
% 17.76/17.95  thf('76', plain,
% 17.76/17.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 17.76/17.95         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 17.76/17.95          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 17.76/17.95      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 17.76/17.95  thf('77', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k9_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 17.76/17.95          (k1_zfmisc_1 @ X0))),
% 17.76/17.95      inference('sup-', [status(thm)], ['75', '76'])).
% 17.76/17.95  thf('78', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 17.76/17.95          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('sup+', [status(thm)], ['72', '77'])).
% 17.76/17.95  thf('79', plain,
% 17.76/17.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('80', plain,
% 17.76/17.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.76/17.95         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 17.76/17.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 17.76/17.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 17.76/17.95  thf('81', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 17.76/17.95           = (k3_xboole_0 @ X0 @ sk_B))),
% 17.76/17.95      inference('sup-', [status(thm)], ['79', '80'])).
% 17.76/17.95  thf('82', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 17.76/17.95          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.76/17.95      inference('demod', [status(thm)], ['78', '81'])).
% 17.76/17.95  thf('83', plain,
% 17.76/17.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 17.76/17.95         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 17.76/17.95          | ~ (r1_tarski @ X21 @ X23)
% 17.76/17.95          | (r1_tarski @ (k2_pre_topc @ X22 @ X21) @ (k2_pre_topc @ X22 @ X23))
% 17.76/17.95          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 17.76/17.95          | ~ (l1_pre_topc @ X22))),
% 17.76/17.95      inference('cnf', [status(esa)], [t49_pre_topc])).
% 17.76/17.95  thf('84', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (~ (l1_pre_topc @ sk_A)
% 17.76/17.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.76/17.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 17.76/17.95             (k2_pre_topc @ sk_A @ X1))
% 17.76/17.95          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1))),
% 17.76/17.95      inference('sup-', [status(thm)], ['82', '83'])).
% 17.76/17.95  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 17.76/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.76/17.95  thf('86', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.76/17.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 17.76/17.95             (k2_pre_topc @ sk_A @ X1))
% 17.76/17.95          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1))),
% 17.76/17.95      inference('demod', [status(thm)], ['84', '85'])).
% 17.76/17.95  thf('87', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 17.76/17.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 17.76/17.95             (k2_pre_topc @ sk_A @ sk_B)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['61', '86'])).
% 17.76/17.95  thf('88', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.76/17.95      inference('demod', [status(thm)], ['21', '24'])).
% 17.76/17.95  thf('89', plain,
% 17.76/17.95      (![X0 : $i]:
% 17.76/17.95         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 17.76/17.95          (k2_pre_topc @ sk_A @ sk_B))),
% 17.76/17.95      inference('demod', [status(thm)], ['87', '88'])).
% 17.76/17.95  thf('90', plain,
% 17.76/17.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.76/17.95         (~ (r1_tarski @ X5 @ X6)
% 17.76/17.95          | ~ (r1_tarski @ X5 @ X7)
% 17.76/17.95          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 17.76/17.95      inference('cnf', [status(esa)], [t19_xboole_1])).
% 17.76/17.95  thf('91', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]:
% 17.76/17.95         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 17.76/17.95           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X1))
% 17.76/17.95          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 17.76/17.95               X1))),
% 17.76/17.95      inference('sup-', [status(thm)], ['89', '90'])).
% 17.76/17.95  thf('92', plain,
% 17.76/17.95      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)) @ 
% 17.76/17.95        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.76/17.95         (k2_pre_topc @ sk_A @ sk_C)))),
% 17.76/17.95      inference('sup-', [status(thm)], ['60', '91'])).
% 17.76/17.95  thf('93', plain,
% 17.76/17.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.76/17.95      inference('demod', [status(thm)], ['30', '31'])).
% 17.76/17.95  thf('94', plain,
% 17.76/17.95      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 17.76/17.95        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.76/17.95         (k2_pre_topc @ sk_A @ sk_C)))),
% 17.76/17.95      inference('demod', [status(thm)], ['92', '93'])).
% 17.76/17.95  thf('95', plain, ($false), inference('demod', [status(thm)], ['12', '94'])).
% 17.76/17.95  
% 17.76/17.95  % SZS output end Refutation
% 17.76/17.95  
% 17.76/17.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
