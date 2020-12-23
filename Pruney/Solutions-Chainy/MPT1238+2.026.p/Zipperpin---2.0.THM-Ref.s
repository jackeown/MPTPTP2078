%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iixxRfY1XO

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:59 EST 2020

% Result     : Theorem 24.11s
% Output     : Refutation 24.11s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 129 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  716 (1703 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
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
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('53',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['20','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iixxRfY1XO
% 0.13/0.37  % Computer   : n010.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:55:14 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 24.11/24.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 24.11/24.32  % Solved by: fo/fo7.sh
% 24.11/24.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.11/24.32  % done 22139 iterations in 23.825s
% 24.11/24.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 24.11/24.32  % SZS output start Refutation
% 24.11/24.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 24.11/24.32  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 24.11/24.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 24.11/24.32  thf(sk_A_type, type, sk_A: $i).
% 24.11/24.32  thf(sk_C_type, type, sk_C: $i).
% 24.11/24.32  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 24.11/24.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 24.11/24.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.11/24.32  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 24.11/24.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 24.11/24.32  thf(sk_B_type, type, sk_B: $i).
% 24.11/24.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 24.11/24.32  thf(t49_tops_1, conjecture,
% 24.11/24.32    (![A:$i]:
% 24.11/24.32     ( ( l1_pre_topc @ A ) =>
% 24.11/24.32       ( ![B:$i]:
% 24.11/24.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.11/24.32           ( ![C:$i]:
% 24.11/24.32             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.11/24.32               ( r1_tarski @
% 24.11/24.32                 ( k4_subset_1 @
% 24.11/24.32                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 24.11/24.32                   ( k1_tops_1 @ A @ C ) ) @ 
% 24.11/24.32                 ( k1_tops_1 @
% 24.11/24.32                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 24.11/24.32  thf(zf_stmt_0, negated_conjecture,
% 24.11/24.32    (~( ![A:$i]:
% 24.11/24.32        ( ( l1_pre_topc @ A ) =>
% 24.11/24.32          ( ![B:$i]:
% 24.11/24.32            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.11/24.32              ( ![C:$i]:
% 24.11/24.32                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.11/24.32                  ( r1_tarski @
% 24.11/24.32                    ( k4_subset_1 @
% 24.11/24.32                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 24.11/24.32                      ( k1_tops_1 @ A @ C ) ) @ 
% 24.11/24.32                    ( k1_tops_1 @
% 24.11/24.32                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 24.11/24.32    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 24.11/24.32  thf('0', plain,
% 24.11/24.32      (~ (r1_tarski @ 
% 24.11/24.32          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 24.11/24.32           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 24.11/24.32          (k1_tops_1 @ sk_A @ 
% 24.11/24.32           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('1', plain,
% 24.11/24.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('2', plain,
% 24.11/24.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf(redefinition_k4_subset_1, axiom,
% 24.11/24.32    (![A:$i,B:$i,C:$i]:
% 24.11/24.32     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 24.11/24.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 24.11/24.32       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 24.11/24.32  thf('3', plain,
% 24.11/24.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.11/24.32         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 24.11/24.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 24.11/24.32          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 24.11/24.32      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 24.11/24.32  thf('4', plain,
% 24.11/24.32      (![X0 : $i]:
% 24.11/24.32         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 24.11/24.32            = (k2_xboole_0 @ sk_B @ X0))
% 24.11/24.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 24.11/24.32      inference('sup-', [status(thm)], ['2', '3'])).
% 24.11/24.32  thf('5', plain,
% 24.11/24.32      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 24.11/24.32         = (k2_xboole_0 @ sk_B @ sk_C))),
% 24.11/24.32      inference('sup-', [status(thm)], ['1', '4'])).
% 24.11/24.32  thf('6', plain,
% 24.11/24.32      (~ (r1_tarski @ 
% 24.11/24.32          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 24.11/24.32           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 24.11/24.32          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 24.11/24.32      inference('demod', [status(thm)], ['0', '5'])).
% 24.11/24.32  thf('7', plain,
% 24.11/24.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf(dt_k1_tops_1, axiom,
% 24.11/24.32    (![A:$i,B:$i]:
% 24.11/24.32     ( ( ( l1_pre_topc @ A ) & 
% 24.11/24.32         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 24.11/24.32       ( m1_subset_1 @
% 24.11/24.32         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 24.11/24.32  thf('8', plain,
% 24.11/24.32      (![X19 : $i, X20 : $i]:
% 24.11/24.32         (~ (l1_pre_topc @ X19)
% 24.11/24.32          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 24.11/24.32          | (m1_subset_1 @ (k1_tops_1 @ X19 @ X20) @ 
% 24.11/24.32             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 24.11/24.32      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 24.11/24.32  thf('9', plain,
% 24.11/24.32      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 24.11/24.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.11/24.32        | ~ (l1_pre_topc @ sk_A))),
% 24.11/24.32      inference('sup-', [status(thm)], ['7', '8'])).
% 24.11/24.32  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('11', plain,
% 24.11/24.32      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 24.11/24.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('demod', [status(thm)], ['9', '10'])).
% 24.11/24.32  thf('12', plain,
% 24.11/24.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('13', plain,
% 24.11/24.32      (![X19 : $i, X20 : $i]:
% 24.11/24.32         (~ (l1_pre_topc @ X19)
% 24.11/24.32          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 24.11/24.32          | (m1_subset_1 @ (k1_tops_1 @ X19 @ X20) @ 
% 24.11/24.32             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 24.11/24.32      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 24.11/24.32  thf('14', plain,
% 24.11/24.32      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 24.11/24.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.11/24.32        | ~ (l1_pre_topc @ sk_A))),
% 24.11/24.32      inference('sup-', [status(thm)], ['12', '13'])).
% 24.11/24.32  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('16', plain,
% 24.11/24.32      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 24.11/24.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('demod', [status(thm)], ['14', '15'])).
% 24.11/24.32  thf('17', plain,
% 24.11/24.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.11/24.32         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 24.11/24.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 24.11/24.32          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 24.11/24.32      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 24.11/24.32  thf('18', plain,
% 24.11/24.32      (![X0 : $i]:
% 24.11/24.32         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 24.11/24.32            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 24.11/24.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 24.11/24.32      inference('sup-', [status(thm)], ['16', '17'])).
% 24.11/24.32  thf('19', plain,
% 24.11/24.32      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 24.11/24.32         (k1_tops_1 @ sk_A @ sk_C))
% 24.11/24.32         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 24.11/24.32      inference('sup-', [status(thm)], ['11', '18'])).
% 24.11/24.32  thf('20', plain,
% 24.11/24.32      (~ (r1_tarski @ 
% 24.11/24.32          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 24.11/24.32          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 24.11/24.32      inference('demod', [status(thm)], ['6', '19'])).
% 24.11/24.32  thf('21', plain,
% 24.11/24.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf(t3_subset, axiom,
% 24.11/24.32    (![A:$i,B:$i]:
% 24.11/24.32     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 24.11/24.32  thf('22', plain,
% 24.11/24.32      (![X16 : $i, X17 : $i]:
% 24.11/24.32         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 24.11/24.32      inference('cnf', [status(esa)], [t3_subset])).
% 24.11/24.32  thf('23', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 24.11/24.32      inference('sup-', [status(thm)], ['21', '22'])).
% 24.11/24.32  thf('24', plain,
% 24.11/24.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('25', plain,
% 24.11/24.32      (![X16 : $i, X17 : $i]:
% 24.11/24.32         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 24.11/24.32      inference('cnf', [status(esa)], [t3_subset])).
% 24.11/24.32  thf('26', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 24.11/24.32      inference('sup-', [status(thm)], ['24', '25'])).
% 24.11/24.32  thf(t8_xboole_1, axiom,
% 24.11/24.32    (![A:$i,B:$i,C:$i]:
% 24.11/24.32     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 24.11/24.32       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 24.11/24.32  thf('27', plain,
% 24.11/24.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 24.11/24.32         (~ (r1_tarski @ X10 @ X11)
% 24.11/24.32          | ~ (r1_tarski @ X12 @ X11)
% 24.11/24.32          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 24.11/24.32      inference('cnf', [status(esa)], [t8_xboole_1])).
% 24.11/24.32  thf('28', plain,
% 24.11/24.32      (![X0 : $i]:
% 24.11/24.32         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))
% 24.11/24.32          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('sup-', [status(thm)], ['26', '27'])).
% 24.11/24.32  thf('29', plain,
% 24.11/24.32      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ (u1_struct_0 @ sk_A))),
% 24.11/24.32      inference('sup-', [status(thm)], ['23', '28'])).
% 24.11/24.32  thf('30', plain,
% 24.11/24.32      (![X16 : $i, X18 : $i]:
% 24.11/24.32         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 24.11/24.32      inference('cnf', [status(esa)], [t3_subset])).
% 24.11/24.32  thf('31', plain,
% 24.11/24.32      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 24.11/24.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('sup-', [status(thm)], ['29', '30'])).
% 24.11/24.32  thf('32', plain,
% 24.11/24.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf(t48_tops_1, axiom,
% 24.11/24.32    (![A:$i]:
% 24.11/24.32     ( ( l1_pre_topc @ A ) =>
% 24.11/24.32       ( ![B:$i]:
% 24.11/24.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.11/24.32           ( ![C:$i]:
% 24.11/24.32             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.11/24.32               ( ( r1_tarski @ B @ C ) =>
% 24.11/24.32                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 24.11/24.32  thf('33', plain,
% 24.11/24.32      (![X21 : $i, X22 : $i, X23 : $i]:
% 24.11/24.32         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 24.11/24.32          | ~ (r1_tarski @ X21 @ X23)
% 24.11/24.32          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ (k1_tops_1 @ X22 @ X23))
% 24.11/24.32          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 24.11/24.32          | ~ (l1_pre_topc @ X22))),
% 24.11/24.32      inference('cnf', [status(esa)], [t48_tops_1])).
% 24.11/24.32  thf('34', plain,
% 24.11/24.32      (![X0 : $i]:
% 24.11/24.32         (~ (l1_pre_topc @ sk_A)
% 24.11/24.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.11/24.32          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 24.11/24.32          | ~ (r1_tarski @ sk_C @ X0))),
% 24.11/24.32      inference('sup-', [status(thm)], ['32', '33'])).
% 24.11/24.32  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('36', plain,
% 24.11/24.32      (![X0 : $i]:
% 24.11/24.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.11/24.32          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 24.11/24.32          | ~ (r1_tarski @ sk_C @ X0))),
% 24.11/24.32      inference('demod', [status(thm)], ['34', '35'])).
% 24.11/24.32  thf('37', plain,
% 24.11/24.32      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))
% 24.11/24.32        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 24.11/24.32           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 24.11/24.32      inference('sup-', [status(thm)], ['31', '36'])).
% 24.11/24.32  thf(d10_xboole_0, axiom,
% 24.11/24.32    (![A:$i,B:$i]:
% 24.11/24.32     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 24.11/24.32  thf('38', plain,
% 24.11/24.32      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 24.11/24.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.11/24.32  thf('39', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 24.11/24.32      inference('simplify', [status(thm)], ['38'])).
% 24.11/24.32  thf(t44_xboole_1, axiom,
% 24.11/24.32    (![A:$i,B:$i,C:$i]:
% 24.11/24.32     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 24.11/24.32       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 24.11/24.32  thf('40', plain,
% 24.11/24.32      (![X5 : $i, X6 : $i, X7 : $i]:
% 24.11/24.32         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 24.11/24.32          | ~ (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7))),
% 24.11/24.32      inference('cnf', [status(esa)], [t44_xboole_1])).
% 24.11/24.32  thf('41', plain,
% 24.11/24.32      (![X0 : $i, X1 : $i]:
% 24.11/24.32         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 24.11/24.32      inference('sup-', [status(thm)], ['39', '40'])).
% 24.11/24.32  thf(t39_xboole_1, axiom,
% 24.11/24.32    (![A:$i,B:$i]:
% 24.11/24.32     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 24.11/24.32  thf('42', plain,
% 24.11/24.32      (![X3 : $i, X4 : $i]:
% 24.11/24.32         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 24.11/24.32           = (k2_xboole_0 @ X3 @ X4))),
% 24.11/24.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 24.11/24.32  thf('43', plain,
% 24.11/24.32      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 24.11/24.32      inference('demod', [status(thm)], ['41', '42'])).
% 24.11/24.32  thf('44', plain,
% 24.11/24.32      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 24.11/24.32        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 24.11/24.32      inference('demod', [status(thm)], ['37', '43'])).
% 24.11/24.32  thf('45', plain,
% 24.11/24.32      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 24.11/24.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('sup-', [status(thm)], ['29', '30'])).
% 24.11/24.32  thf('46', plain,
% 24.11/24.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('47', plain,
% 24.11/24.32      (![X21 : $i, X22 : $i, X23 : $i]:
% 24.11/24.32         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 24.11/24.32          | ~ (r1_tarski @ X21 @ X23)
% 24.11/24.32          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ (k1_tops_1 @ X22 @ X23))
% 24.11/24.32          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 24.11/24.32          | ~ (l1_pre_topc @ X22))),
% 24.11/24.32      inference('cnf', [status(esa)], [t48_tops_1])).
% 24.11/24.32  thf('48', plain,
% 24.11/24.32      (![X0 : $i]:
% 24.11/24.32         (~ (l1_pre_topc @ sk_A)
% 24.11/24.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.11/24.32          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 24.11/24.32          | ~ (r1_tarski @ sk_B @ X0))),
% 24.11/24.32      inference('sup-', [status(thm)], ['46', '47'])).
% 24.11/24.32  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 24.11/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.11/24.32  thf('50', plain,
% 24.11/24.32      (![X0 : $i]:
% 24.11/24.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.11/24.32          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 24.11/24.32          | ~ (r1_tarski @ sk_B @ X0))),
% 24.11/24.32      inference('demod', [status(thm)], ['48', '49'])).
% 24.11/24.32  thf('51', plain,
% 24.11/24.32      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 24.11/24.32        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 24.11/24.32           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 24.11/24.32      inference('sup-', [status(thm)], ['45', '50'])).
% 24.11/24.32  thf(t7_xboole_1, axiom,
% 24.11/24.32    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 24.11/24.32  thf('52', plain,
% 24.11/24.32      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 24.11/24.32      inference('cnf', [status(esa)], [t7_xboole_1])).
% 24.11/24.32  thf('53', plain,
% 24.11/24.32      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 24.11/24.32        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 24.11/24.32      inference('demod', [status(thm)], ['51', '52'])).
% 24.11/24.32  thf('54', plain,
% 24.11/24.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 24.11/24.32         (~ (r1_tarski @ X10 @ X11)
% 24.11/24.32          | ~ (r1_tarski @ X12 @ X11)
% 24.11/24.32          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 24.11/24.32      inference('cnf', [status(esa)], [t8_xboole_1])).
% 24.11/24.32  thf('55', plain,
% 24.11/24.32      (![X0 : $i]:
% 24.11/24.32         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 24.11/24.32           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 24.11/24.32          | ~ (r1_tarski @ X0 @ 
% 24.11/24.32               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 24.11/24.32      inference('sup-', [status(thm)], ['53', '54'])).
% 24.11/24.32  thf('56', plain,
% 24.11/24.32      ((r1_tarski @ 
% 24.11/24.32        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 24.11/24.32        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 24.11/24.32      inference('sup-', [status(thm)], ['44', '55'])).
% 24.11/24.32  thf('57', plain, ($false), inference('demod', [status(thm)], ['20', '56'])).
% 24.11/24.32  
% 24.11/24.32  % SZS output end Refutation
% 24.11/24.32  
% 24.11/24.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
