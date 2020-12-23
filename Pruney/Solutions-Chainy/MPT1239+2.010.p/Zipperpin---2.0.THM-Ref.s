%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.29DgrtjDX7

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:02 EST 2020

% Result     : Theorem 8.60s
% Output     : Refutation 8.60s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 108 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  636 (1346 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['12','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.29DgrtjDX7
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:17:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 8.60/8.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.60/8.85  % Solved by: fo/fo7.sh
% 8.60/8.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.60/8.85  % done 9468 iterations in 8.395s
% 8.60/8.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.60/8.85  % SZS output start Refutation
% 8.60/8.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.60/8.85  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.60/8.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.60/8.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.60/8.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.60/8.85  thf(sk_B_type, type, sk_B: $i).
% 8.60/8.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.60/8.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.60/8.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.60/8.85  thf(sk_C_type, type, sk_C: $i).
% 8.60/8.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.60/8.85  thf(sk_A_type, type, sk_A: $i).
% 8.60/8.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.60/8.85  thf(t50_tops_1, conjecture,
% 8.60/8.85    (![A:$i]:
% 8.60/8.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.60/8.85       ( ![B:$i]:
% 8.60/8.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.60/8.85           ( ![C:$i]:
% 8.60/8.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.60/8.85               ( r1_tarski @
% 8.60/8.85                 ( k1_tops_1 @
% 8.60/8.85                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 8.60/8.85                 ( k7_subset_1 @
% 8.60/8.85                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 8.60/8.85                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.60/8.85  thf(zf_stmt_0, negated_conjecture,
% 8.60/8.85    (~( ![A:$i]:
% 8.60/8.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.60/8.85          ( ![B:$i]:
% 8.60/8.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.60/8.85              ( ![C:$i]:
% 8.60/8.85                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.60/8.85                  ( r1_tarski @
% 8.60/8.85                    ( k1_tops_1 @
% 8.60/8.85                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 8.60/8.85                    ( k7_subset_1 @
% 8.60/8.85                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 8.60/8.85                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 8.60/8.85    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 8.60/8.85  thf('0', plain,
% 8.60/8.85      (~ (r1_tarski @ 
% 8.60/8.85          (k1_tops_1 @ sk_A @ 
% 8.60/8.85           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 8.60/8.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.60/8.85           (k1_tops_1 @ sk_A @ sk_C)))),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf('1', plain,
% 8.60/8.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf(redefinition_k7_subset_1, axiom,
% 8.60/8.85    (![A:$i,B:$i,C:$i]:
% 8.60/8.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.60/8.85       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.60/8.85  thf('2', plain,
% 8.60/8.85      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.60/8.85         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 8.60/8.85          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 8.60/8.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.60/8.85  thf('3', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.60/8.85           = (k4_xboole_0 @ sk_B @ X0))),
% 8.60/8.85      inference('sup-', [status(thm)], ['1', '2'])).
% 8.60/8.85  thf('4', plain,
% 8.60/8.85      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.60/8.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.60/8.85           (k1_tops_1 @ sk_A @ sk_C)))),
% 8.60/8.85      inference('demod', [status(thm)], ['0', '3'])).
% 8.60/8.85  thf('5', plain,
% 8.60/8.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf(dt_k1_tops_1, axiom,
% 8.60/8.85    (![A:$i,B:$i]:
% 8.60/8.85     ( ( ( l1_pre_topc @ A ) & 
% 8.60/8.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.60/8.85       ( m1_subset_1 @
% 8.60/8.85         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.60/8.85  thf('6', plain,
% 8.60/8.85      (![X24 : $i, X25 : $i]:
% 8.60/8.85         (~ (l1_pre_topc @ X24)
% 8.60/8.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.60/8.85          | (m1_subset_1 @ (k1_tops_1 @ X24 @ X25) @ 
% 8.60/8.85             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 8.60/8.85      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 8.60/8.85  thf('7', plain,
% 8.60/8.85      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.60/8.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.60/8.85        | ~ (l1_pre_topc @ sk_A))),
% 8.60/8.85      inference('sup-', [status(thm)], ['5', '6'])).
% 8.60/8.85  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf('9', plain,
% 8.60/8.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.60/8.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.60/8.85      inference('demod', [status(thm)], ['7', '8'])).
% 8.60/8.85  thf('10', plain,
% 8.60/8.85      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.60/8.85         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 8.60/8.85          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 8.60/8.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.60/8.85  thf('11', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 8.60/8.85           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 8.60/8.85      inference('sup-', [status(thm)], ['9', '10'])).
% 8.60/8.85  thf('12', plain,
% 8.60/8.85      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.60/8.85          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.60/8.85      inference('demod', [status(thm)], ['4', '11'])).
% 8.60/8.85  thf('13', plain,
% 8.60/8.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf('14', plain,
% 8.60/8.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf(t3_subset, axiom,
% 8.60/8.85    (![A:$i,B:$i]:
% 8.60/8.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.60/8.85  thf('15', plain,
% 8.60/8.85      (![X21 : $i, X22 : $i]:
% 8.60/8.85         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 8.60/8.85      inference('cnf', [status(esa)], [t3_subset])).
% 8.60/8.85  thf('16', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.60/8.85      inference('sup-', [status(thm)], ['14', '15'])).
% 8.60/8.85  thf(t109_xboole_1, axiom,
% 8.60/8.85    (![A:$i,B:$i,C:$i]:
% 8.60/8.85     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 8.60/8.85  thf('17', plain,
% 8.60/8.85      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.60/8.85         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 8.60/8.85      inference('cnf', [status(esa)], [t109_xboole_1])).
% 8.60/8.85  thf('18', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 8.60/8.85      inference('sup-', [status(thm)], ['16', '17'])).
% 8.60/8.85  thf('19', plain,
% 8.60/8.85      (![X21 : $i, X23 : $i]:
% 8.60/8.85         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 8.60/8.85      inference('cnf', [status(esa)], [t3_subset])).
% 8.60/8.85  thf('20', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 8.60/8.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.60/8.85      inference('sup-', [status(thm)], ['18', '19'])).
% 8.60/8.85  thf(t48_tops_1, axiom,
% 8.60/8.85    (![A:$i]:
% 8.60/8.85     ( ( l1_pre_topc @ A ) =>
% 8.60/8.85       ( ![B:$i]:
% 8.60/8.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.60/8.85           ( ![C:$i]:
% 8.60/8.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.60/8.85               ( ( r1_tarski @ B @ C ) =>
% 8.60/8.85                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.60/8.85  thf('21', plain,
% 8.60/8.85      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.60/8.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 8.60/8.85          | ~ (r1_tarski @ X28 @ X30)
% 8.60/8.85          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 8.60/8.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 8.60/8.85          | ~ (l1_pre_topc @ X29))),
% 8.60/8.85      inference('cnf', [status(esa)], [t48_tops_1])).
% 8.60/8.85  thf('22', plain,
% 8.60/8.85      (![X0 : $i, X1 : $i]:
% 8.60/8.85         (~ (l1_pre_topc @ sk_A)
% 8.60/8.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.60/8.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.60/8.85             (k1_tops_1 @ sk_A @ X1))
% 8.60/8.85          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.60/8.85      inference('sup-', [status(thm)], ['20', '21'])).
% 8.60/8.85  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf('24', plain,
% 8.60/8.85      (![X0 : $i, X1 : $i]:
% 8.60/8.85         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.60/8.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.60/8.85             (k1_tops_1 @ sk_A @ X1))
% 8.60/8.85          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.60/8.85      inference('demod', [status(thm)], ['22', '23'])).
% 8.60/8.85  thf('25', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 8.60/8.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.60/8.85             (k1_tops_1 @ sk_A @ sk_B)))),
% 8.60/8.85      inference('sup-', [status(thm)], ['13', '24'])).
% 8.60/8.85  thf(t36_xboole_1, axiom,
% 8.60/8.85    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.60/8.85  thf('26', plain,
% 8.60/8.85      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 8.60/8.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.60/8.85  thf('27', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.60/8.85          (k1_tops_1 @ sk_A @ sk_B))),
% 8.60/8.85      inference('demod', [status(thm)], ['25', '26'])).
% 8.60/8.85  thf('28', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 8.60/8.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.60/8.85      inference('sup-', [status(thm)], ['18', '19'])).
% 8.60/8.85  thf(t44_tops_1, axiom,
% 8.60/8.85    (![A:$i]:
% 8.60/8.85     ( ( l1_pre_topc @ A ) =>
% 8.60/8.85       ( ![B:$i]:
% 8.60/8.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.60/8.85           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 8.60/8.85  thf('29', plain,
% 8.60/8.85      (![X26 : $i, X27 : $i]:
% 8.60/8.85         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 8.60/8.85          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 8.60/8.85          | ~ (l1_pre_topc @ X27))),
% 8.60/8.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.60/8.85  thf('30', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         (~ (l1_pre_topc @ sk_A)
% 8.60/8.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.60/8.85             (k4_xboole_0 @ sk_B @ X0)))),
% 8.60/8.85      inference('sup-', [status(thm)], ['28', '29'])).
% 8.60/8.85  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf('32', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.60/8.85          (k4_xboole_0 @ sk_B @ X0))),
% 8.60/8.85      inference('demod', [status(thm)], ['30', '31'])).
% 8.60/8.85  thf(t106_xboole_1, axiom,
% 8.60/8.85    (![A:$i,B:$i,C:$i]:
% 8.60/8.85     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 8.60/8.85       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 8.60/8.85  thf('33', plain,
% 8.60/8.85      (![X3 : $i, X4 : $i, X5 : $i]:
% 8.60/8.85         ((r1_xboole_0 @ X3 @ X5)
% 8.60/8.85          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 8.60/8.85      inference('cnf', [status(esa)], [t106_xboole_1])).
% 8.60/8.85  thf('34', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X0)),
% 8.60/8.85      inference('sup-', [status(thm)], ['32', '33'])).
% 8.60/8.85  thf('35', plain,
% 8.60/8.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf('36', plain,
% 8.60/8.85      (![X26 : $i, X27 : $i]:
% 8.60/8.85         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 8.60/8.85          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 8.60/8.85          | ~ (l1_pre_topc @ X27))),
% 8.60/8.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.60/8.85  thf('37', plain,
% 8.60/8.85      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 8.60/8.85      inference('sup-', [status(thm)], ['35', '36'])).
% 8.60/8.85  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 8.60/8.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.60/8.85  thf('39', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 8.60/8.85      inference('demod', [status(thm)], ['37', '38'])).
% 8.60/8.85  thf(d10_xboole_0, axiom,
% 8.60/8.85    (![A:$i,B:$i]:
% 8.60/8.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.60/8.85  thf('40', plain,
% 8.60/8.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.60/8.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.60/8.85  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.60/8.85      inference('simplify', [status(thm)], ['40'])).
% 8.60/8.85  thf(t64_xboole_1, axiom,
% 8.60/8.85    (![A:$i,B:$i,C:$i,D:$i]:
% 8.60/8.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 8.60/8.85         ( r1_xboole_0 @ B @ D ) ) =>
% 8.60/8.85       ( r1_xboole_0 @ A @ C ) ))).
% 8.60/8.85  thf('42', plain,
% 8.60/8.85      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 8.60/8.85         ((r1_xboole_0 @ X11 @ X12)
% 8.60/8.85          | ~ (r1_tarski @ X11 @ X13)
% 8.60/8.85          | ~ (r1_tarski @ X12 @ X14)
% 8.60/8.85          | ~ (r1_xboole_0 @ X13 @ X14))),
% 8.60/8.85      inference('cnf', [status(esa)], [t64_xboole_1])).
% 8.60/8.85  thf('43', plain,
% 8.60/8.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.60/8.85         (~ (r1_xboole_0 @ X0 @ X1)
% 8.60/8.85          | ~ (r1_tarski @ X2 @ X1)
% 8.60/8.85          | (r1_xboole_0 @ X0 @ X2))),
% 8.60/8.85      inference('sup-', [status(thm)], ['41', '42'])).
% 8.60/8.85  thf('44', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         ((r1_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 8.60/8.85          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 8.60/8.85      inference('sup-', [status(thm)], ['39', '43'])).
% 8.60/8.85  thf('45', plain,
% 8.60/8.85      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.60/8.85        (k1_tops_1 @ sk_A @ sk_C))),
% 8.60/8.85      inference('sup-', [status(thm)], ['34', '44'])).
% 8.60/8.85  thf(t86_xboole_1, axiom,
% 8.60/8.85    (![A:$i,B:$i,C:$i]:
% 8.60/8.85     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 8.60/8.85       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 8.60/8.85  thf('46', plain,
% 8.60/8.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 8.60/8.85         (~ (r1_tarski @ X15 @ X16)
% 8.60/8.85          | ~ (r1_xboole_0 @ X15 @ X17)
% 8.60/8.85          | (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 8.60/8.85      inference('cnf', [status(esa)], [t86_xboole_1])).
% 8.60/8.85  thf('47', plain,
% 8.60/8.85      (![X0 : $i]:
% 8.60/8.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.60/8.85           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 8.60/8.85          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.60/8.85               X0))),
% 8.60/8.85      inference('sup-', [status(thm)], ['45', '46'])).
% 8.60/8.85  thf('48', plain,
% 8.60/8.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.60/8.85        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.60/8.85      inference('sup-', [status(thm)], ['27', '47'])).
% 8.60/8.85  thf('49', plain, ($false), inference('demod', [status(thm)], ['12', '48'])).
% 8.60/8.85  
% 8.60/8.85  % SZS output end Refutation
% 8.60/8.85  
% 8.60/8.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
