%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fwr7gCIvIH

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:59 EST 2020

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 129 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  686 (1966 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X12 @ X11 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( r1_tarski @ ( k1_tops_1 @ X20 @ X19 ) @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( r1_tarski @ ( k1_tops_1 @ X20 @ X19 ) @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['20','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fwr7gCIvIH
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.01/3.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.01/3.24  % Solved by: fo/fo7.sh
% 3.01/3.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.01/3.24  % done 2267 iterations in 2.769s
% 3.01/3.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.01/3.24  % SZS output start Refutation
% 3.01/3.24  thf(sk_C_type, type, sk_C: $i).
% 3.01/3.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.01/3.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.01/3.24  thf(sk_B_type, type, sk_B: $i).
% 3.01/3.24  thf(sk_A_type, type, sk_A: $i).
% 3.01/3.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.01/3.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.01/3.24  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.01/3.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.01/3.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.01/3.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.01/3.24  thf(t49_tops_1, conjecture,
% 3.01/3.24    (![A:$i]:
% 3.01/3.24     ( ( l1_pre_topc @ A ) =>
% 3.01/3.24       ( ![B:$i]:
% 3.01/3.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.24           ( ![C:$i]:
% 3.01/3.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.24               ( r1_tarski @
% 3.01/3.24                 ( k4_subset_1 @
% 3.01/3.24                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 3.01/3.24                   ( k1_tops_1 @ A @ C ) ) @ 
% 3.01/3.24                 ( k1_tops_1 @
% 3.01/3.24                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 3.01/3.24  thf(zf_stmt_0, negated_conjecture,
% 3.01/3.24    (~( ![A:$i]:
% 3.01/3.24        ( ( l1_pre_topc @ A ) =>
% 3.01/3.24          ( ![B:$i]:
% 3.01/3.24            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.24              ( ![C:$i]:
% 3.01/3.24                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.24                  ( r1_tarski @
% 3.01/3.24                    ( k4_subset_1 @
% 3.01/3.24                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 3.01/3.24                      ( k1_tops_1 @ A @ C ) ) @ 
% 3.01/3.24                    ( k1_tops_1 @
% 3.01/3.24                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 3.01/3.24    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 3.01/3.24  thf('0', plain,
% 3.01/3.24      (~ (r1_tarski @ 
% 3.01/3.24          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.01/3.24           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.01/3.24          (k1_tops_1 @ sk_A @ 
% 3.01/3.24           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('1', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('2', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(redefinition_k4_subset_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.01/3.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.01/3.24       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.01/3.24  thf('3', plain,
% 3.01/3.24      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.01/3.24          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 3.01/3.24          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 3.01/3.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.01/3.24  thf('4', plain,
% 3.01/3.24      (![X0 : $i]:
% 3.01/3.24         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.01/3.24            = (k2_xboole_0 @ sk_B @ X0))
% 3.01/3.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['2', '3'])).
% 3.01/3.24  thf('5', plain,
% 3.01/3.24      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 3.01/3.24         = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.01/3.24      inference('sup-', [status(thm)], ['1', '4'])).
% 3.01/3.24  thf('6', plain,
% 3.01/3.24      (~ (r1_tarski @ 
% 3.01/3.24          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.01/3.24           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.01/3.24          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.01/3.24      inference('demod', [status(thm)], ['0', '5'])).
% 3.01/3.24  thf('7', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(dt_k1_tops_1, axiom,
% 3.01/3.24    (![A:$i,B:$i]:
% 3.01/3.24     ( ( ( l1_pre_topc @ A ) & 
% 3.01/3.24         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.01/3.24       ( m1_subset_1 @
% 3.01/3.24         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.01/3.24  thf('8', plain,
% 3.01/3.24      (![X17 : $i, X18 : $i]:
% 3.01/3.24         (~ (l1_pre_topc @ X17)
% 3.01/3.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.01/3.24          | (m1_subset_1 @ (k1_tops_1 @ X17 @ X18) @ 
% 3.01/3.24             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 3.01/3.24      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.01/3.24  thf('9', plain,
% 3.01/3.24      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.01/3.24         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.01/3.24        | ~ (l1_pre_topc @ sk_A))),
% 3.01/3.24      inference('sup-', [status(thm)], ['7', '8'])).
% 3.01/3.24  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('11', plain,
% 3.01/3.24      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.01/3.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('demod', [status(thm)], ['9', '10'])).
% 3.01/3.24  thf('12', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('13', plain,
% 3.01/3.24      (![X17 : $i, X18 : $i]:
% 3.01/3.24         (~ (l1_pre_topc @ X17)
% 3.01/3.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.01/3.24          | (m1_subset_1 @ (k1_tops_1 @ X17 @ X18) @ 
% 3.01/3.24             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 3.01/3.24      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.01/3.24  thf('14', plain,
% 3.01/3.24      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.01/3.24         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.01/3.24        | ~ (l1_pre_topc @ sk_A))),
% 3.01/3.24      inference('sup-', [status(thm)], ['12', '13'])).
% 3.01/3.24  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('16', plain,
% 3.01/3.24      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.01/3.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('demod', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('17', plain,
% 3.01/3.24      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.01/3.24          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 3.01/3.24          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 3.01/3.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.01/3.24  thf('18', plain,
% 3.01/3.24      (![X0 : $i]:
% 3.01/3.24         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 3.01/3.24            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 3.01/3.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['16', '17'])).
% 3.01/3.24  thf('19', plain,
% 3.01/3.24      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.01/3.24         (k1_tops_1 @ sk_A @ sk_C))
% 3.01/3.24         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['11', '18'])).
% 3.01/3.24  thf('20', plain,
% 3.01/3.24      (~ (r1_tarski @ 
% 3.01/3.24          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.01/3.24          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.01/3.24      inference('demod', [status(thm)], ['6', '19'])).
% 3.01/3.24  thf('21', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('22', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(dt_k4_subset_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.01/3.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.01/3.24       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.01/3.24  thf('23', plain,
% 3.01/3.24      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 3.01/3.24          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 3.01/3.24          | (m1_subset_1 @ (k4_subset_1 @ X12 @ X11 @ X13) @ 
% 3.01/3.24             (k1_zfmisc_1 @ X12)))),
% 3.01/3.24      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 3.01/3.24  thf('24', plain,
% 3.01/3.24      (![X0 : $i]:
% 3.01/3.24         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 3.01/3.24           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.01/3.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['22', '23'])).
% 3.01/3.24  thf('25', plain,
% 3.01/3.24      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 3.01/3.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['21', '24'])).
% 3.01/3.24  thf('26', plain,
% 3.01/3.24      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 3.01/3.24         = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.01/3.24      inference('sup-', [status(thm)], ['1', '4'])).
% 3.01/3.24  thf('27', plain,
% 3.01/3.24      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 3.01/3.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('demod', [status(thm)], ['25', '26'])).
% 3.01/3.24  thf('28', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(t48_tops_1, axiom,
% 3.01/3.24    (![A:$i]:
% 3.01/3.24     ( ( l1_pre_topc @ A ) =>
% 3.01/3.24       ( ![B:$i]:
% 3.01/3.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.24           ( ![C:$i]:
% 3.01/3.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.24               ( ( r1_tarski @ B @ C ) =>
% 3.01/3.24                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.01/3.24  thf('29', plain,
% 3.01/3.24      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.01/3.24          | ~ (r1_tarski @ X19 @ X21)
% 3.01/3.24          | (r1_tarski @ (k1_tops_1 @ X20 @ X19) @ (k1_tops_1 @ X20 @ X21))
% 3.01/3.24          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.01/3.24          | ~ (l1_pre_topc @ X20))),
% 3.01/3.24      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.01/3.24  thf('30', plain,
% 3.01/3.24      (![X0 : $i]:
% 3.01/3.24         (~ (l1_pre_topc @ sk_A)
% 3.01/3.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.01/3.24          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 3.01/3.24          | ~ (r1_tarski @ sk_C @ X0))),
% 3.01/3.24      inference('sup-', [status(thm)], ['28', '29'])).
% 3.01/3.24  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('32', plain,
% 3.01/3.24      (![X0 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.01/3.24          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 3.01/3.24          | ~ (r1_tarski @ sk_C @ X0))),
% 3.01/3.24      inference('demod', [status(thm)], ['30', '31'])).
% 3.01/3.24  thf('33', plain,
% 3.01/3.24      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))
% 3.01/3.24        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.01/3.24           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['27', '32'])).
% 3.01/3.24  thf(d10_xboole_0, axiom,
% 3.01/3.24    (![A:$i,B:$i]:
% 3.01/3.24     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.01/3.24  thf('34', plain,
% 3.01/3.24      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.01/3.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.01/3.24  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.01/3.24      inference('simplify', [status(thm)], ['34'])).
% 3.01/3.24  thf(t10_xboole_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 3.01/3.24  thf('36', plain,
% 3.01/3.24      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.01/3.24         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 3.01/3.24      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.01/3.24  thf('37', plain,
% 3.01/3.24      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.01/3.24      inference('sup-', [status(thm)], ['35', '36'])).
% 3.01/3.24  thf('38', plain,
% 3.01/3.24      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.01/3.24        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.01/3.24      inference('demod', [status(thm)], ['33', '37'])).
% 3.01/3.24  thf('39', plain,
% 3.01/3.24      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 3.01/3.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('demod', [status(thm)], ['25', '26'])).
% 3.01/3.24  thf('40', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('41', plain,
% 3.01/3.24      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.01/3.24          | ~ (r1_tarski @ X19 @ X21)
% 3.01/3.24          | (r1_tarski @ (k1_tops_1 @ X20 @ X19) @ (k1_tops_1 @ X20 @ X21))
% 3.01/3.24          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.01/3.24          | ~ (l1_pre_topc @ X20))),
% 3.01/3.24      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.01/3.24  thf('42', plain,
% 3.01/3.24      (![X0 : $i]:
% 3.01/3.24         (~ (l1_pre_topc @ sk_A)
% 3.01/3.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.01/3.24          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 3.01/3.24          | ~ (r1_tarski @ sk_B @ X0))),
% 3.01/3.24      inference('sup-', [status(thm)], ['40', '41'])).
% 3.01/3.24  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('44', plain,
% 3.01/3.24      (![X0 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.01/3.24          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 3.01/3.24          | ~ (r1_tarski @ sk_B @ X0))),
% 3.01/3.24      inference('demod', [status(thm)], ['42', '43'])).
% 3.01/3.24  thf('45', plain,
% 3.01/3.24      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 3.01/3.24        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.01/3.24           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['39', '44'])).
% 3.01/3.24  thf(t7_xboole_1, axiom,
% 3.01/3.24    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.01/3.24  thf('46', plain,
% 3.01/3.24      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 3.01/3.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.01/3.24  thf('47', plain,
% 3.01/3.24      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.01/3.24        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.01/3.24      inference('demod', [status(thm)], ['45', '46'])).
% 3.01/3.24  thf(t8_xboole_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 3.01/3.24       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.01/3.24  thf('48', plain,
% 3.01/3.24      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.01/3.24         (~ (r1_tarski @ X8 @ X9)
% 3.01/3.24          | ~ (r1_tarski @ X10 @ X9)
% 3.01/3.24          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 3.01/3.24      inference('cnf', [status(esa)], [t8_xboole_1])).
% 3.01/3.24  thf('49', plain,
% 3.01/3.24      (![X0 : $i]:
% 3.01/3.24         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 3.01/3.24           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 3.01/3.24          | ~ (r1_tarski @ X0 @ 
% 3.01/3.24               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['47', '48'])).
% 3.01/3.24  thf('50', plain,
% 3.01/3.24      ((r1_tarski @ 
% 3.01/3.24        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.01/3.24        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['38', '49'])).
% 3.01/3.24  thf('51', plain, ($false), inference('demod', [status(thm)], ['20', '50'])).
% 3.01/3.24  
% 3.01/3.24  % SZS output end Refutation
% 3.01/3.24  
% 3.01/3.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
