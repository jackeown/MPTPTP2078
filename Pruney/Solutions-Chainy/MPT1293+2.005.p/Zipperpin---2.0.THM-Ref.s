%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n8E7w9l0qd

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:07 EST 2020

% Result     : Theorem 4.10s
% Output     : Refutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   79 (  97 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  624 (1101 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t6_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tops_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k5_setfam_1 @ X22 @ X21 )
        = ( k3_tarski @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k5_setfam_1 @ X22 @ X21 )
        = ( k3_tarski @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('6',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k3_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ ( k3_tarski @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('16',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X17: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('18',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ B )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k5_setfam_1 @ X22 @ X21 )
        = ( k3_tarski @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['23','32'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ ( k3_tarski @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X15 ) @ ( k3_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['33','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n8E7w9l0qd
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:05:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 4.10/4.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.10/4.29  % Solved by: fo/fo7.sh
% 4.10/4.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.10/4.29  % done 2516 iterations in 3.844s
% 4.10/4.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.10/4.29  % SZS output start Refutation
% 4.10/4.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.10/4.29  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 4.10/4.29  thf(sk_B_type, type, sk_B: $i).
% 4.10/4.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.10/4.29  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 4.10/4.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.10/4.29  thf(sk_C_type, type, sk_C: $i).
% 4.10/4.29  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.10/4.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.10/4.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.10/4.29  thf(sk_A_type, type, sk_A: $i).
% 4.10/4.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.10/4.29  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.10/4.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.10/4.29  thf(t6_tops_2, conjecture,
% 4.10/4.29    (![A:$i]:
% 4.10/4.29     ( ( l1_struct_0 @ A ) =>
% 4.10/4.29       ( ![B:$i]:
% 4.10/4.29         ( ( m1_subset_1 @
% 4.10/4.29             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.10/4.29           ( ![C:$i]:
% 4.10/4.29             ( ( m1_subset_1 @
% 4.10/4.29                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.10/4.29               ( r1_tarski @
% 4.10/4.29                 ( k7_subset_1 @
% 4.10/4.29                   ( u1_struct_0 @ A ) @ 
% 4.10/4.29                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 4.10/4.29                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 4.10/4.29                 ( k5_setfam_1 @
% 4.10/4.29                   ( u1_struct_0 @ A ) @ 
% 4.10/4.29                   ( k7_subset_1 @
% 4.10/4.29                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 4.10/4.29  thf(zf_stmt_0, negated_conjecture,
% 4.10/4.29    (~( ![A:$i]:
% 4.10/4.29        ( ( l1_struct_0 @ A ) =>
% 4.10/4.29          ( ![B:$i]:
% 4.10/4.29            ( ( m1_subset_1 @
% 4.10/4.29                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.10/4.29              ( ![C:$i]:
% 4.10/4.29                ( ( m1_subset_1 @
% 4.10/4.29                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.10/4.29                  ( r1_tarski @
% 4.10/4.29                    ( k7_subset_1 @
% 4.10/4.29                      ( u1_struct_0 @ A ) @ 
% 4.10/4.29                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 4.10/4.29                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 4.10/4.29                    ( k5_setfam_1 @
% 4.10/4.29                      ( u1_struct_0 @ A ) @ 
% 4.10/4.29                      ( k7_subset_1 @
% 4.10/4.29                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 4.10/4.29    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 4.10/4.29  thf('0', plain,
% 4.10/4.29      (~ (r1_tarski @ 
% 4.10/4.29          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.10/4.29           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 4.10/4.29           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 4.10/4.29          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 4.10/4.29           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 4.10/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.29  thf('1', plain,
% 4.10/4.29      ((m1_subset_1 @ sk_B @ 
% 4.10/4.29        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.10/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.29  thf(redefinition_k5_setfam_1, axiom,
% 4.10/4.29    (![A:$i,B:$i]:
% 4.10/4.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.10/4.29       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 4.10/4.29  thf('2', plain,
% 4.10/4.29      (![X21 : $i, X22 : $i]:
% 4.10/4.29         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 4.10/4.29          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 4.10/4.29      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 4.10/4.29  thf('3', plain,
% 4.10/4.29      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 4.10/4.29      inference('sup-', [status(thm)], ['1', '2'])).
% 4.10/4.29  thf('4', plain,
% 4.10/4.29      ((m1_subset_1 @ sk_C @ 
% 4.10/4.29        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.10/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.29  thf('5', plain,
% 4.10/4.29      (![X21 : $i, X22 : $i]:
% 4.10/4.29         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 4.10/4.29          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 4.10/4.29      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 4.10/4.29  thf('6', plain,
% 4.10/4.29      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 4.10/4.29      inference('sup-', [status(thm)], ['4', '5'])).
% 4.10/4.29  thf('7', plain,
% 4.10/4.29      (~ (r1_tarski @ 
% 4.10/4.29          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 4.10/4.29           (k3_tarski @ sk_C)) @ 
% 4.10/4.29          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 4.10/4.29           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 4.10/4.29      inference('demod', [status(thm)], ['0', '3', '6'])).
% 4.10/4.29  thf('8', plain,
% 4.10/4.29      ((m1_subset_1 @ sk_B @ 
% 4.10/4.29        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.10/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.29  thf(redefinition_k7_subset_1, axiom,
% 4.10/4.29    (![A:$i,B:$i,C:$i]:
% 4.10/4.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.10/4.29       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 4.10/4.29  thf('9', plain,
% 4.10/4.29      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.10/4.29         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 4.10/4.29          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 4.10/4.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.10/4.29  thf('10', plain,
% 4.10/4.29      (![X0 : $i]:
% 4.10/4.29         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 4.10/4.29           = (k4_xboole_0 @ sk_B @ X0))),
% 4.10/4.29      inference('sup-', [status(thm)], ['8', '9'])).
% 4.10/4.29  thf('11', plain,
% 4.10/4.29      (~ (r1_tarski @ 
% 4.10/4.29          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 4.10/4.29           (k3_tarski @ sk_C)) @ 
% 4.10/4.29          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 4.10/4.29      inference('demod', [status(thm)], ['7', '10'])).
% 4.10/4.29  thf('12', plain,
% 4.10/4.29      ((m1_subset_1 @ sk_B @ 
% 4.10/4.29        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.10/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.29  thf(t3_subset, axiom,
% 4.10/4.29    (![A:$i,B:$i]:
% 4.10/4.29     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.10/4.29  thf('13', plain,
% 4.10/4.29      (![X23 : $i, X24 : $i]:
% 4.10/4.29         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 4.10/4.29      inference('cnf', [status(esa)], [t3_subset])).
% 4.10/4.29  thf('14', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.10/4.29      inference('sup-', [status(thm)], ['12', '13'])).
% 4.10/4.29  thf(t95_zfmisc_1, axiom,
% 4.10/4.29    (![A:$i,B:$i]:
% 4.10/4.29     ( ( r1_tarski @ A @ B ) =>
% 4.10/4.29       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 4.10/4.29  thf('15', plain,
% 4.10/4.29      (![X13 : $i, X14 : $i]:
% 4.10/4.29         ((r1_tarski @ (k3_tarski @ X13) @ (k3_tarski @ X14))
% 4.10/4.29          | ~ (r1_tarski @ X13 @ X14))),
% 4.10/4.29      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 4.10/4.29  thf('16', plain,
% 4.10/4.29      ((r1_tarski @ (k3_tarski @ sk_B) @ 
% 4.10/4.29        (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.10/4.29      inference('sup-', [status(thm)], ['14', '15'])).
% 4.10/4.29  thf(t99_zfmisc_1, axiom,
% 4.10/4.29    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 4.10/4.29  thf('17', plain, (![X17 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X17)) = (X17))),
% 4.10/4.29      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 4.10/4.29  thf('18', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ (u1_struct_0 @ sk_A))),
% 4.10/4.29      inference('demod', [status(thm)], ['16', '17'])).
% 4.10/4.29  thf('19', plain,
% 4.10/4.29      (![X23 : $i, X25 : $i]:
% 4.10/4.29         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 4.10/4.29      inference('cnf', [status(esa)], [t3_subset])).
% 4.10/4.29  thf('20', plain,
% 4.10/4.29      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.10/4.29      inference('sup-', [status(thm)], ['18', '19'])).
% 4.10/4.29  thf('21', plain,
% 4.10/4.29      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.10/4.29         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 4.10/4.29          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 4.10/4.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.10/4.29  thf('22', plain,
% 4.10/4.29      (![X0 : $i]:
% 4.10/4.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 4.10/4.29           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 4.10/4.29      inference('sup-', [status(thm)], ['20', '21'])).
% 4.10/4.29  thf('23', plain,
% 4.10/4.29      (~ (r1_tarski @ 
% 4.10/4.29          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 4.10/4.29          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 4.10/4.29      inference('demod', [status(thm)], ['11', '22'])).
% 4.10/4.29  thf(t36_xboole_1, axiom,
% 4.10/4.29    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.10/4.29  thf('24', plain,
% 4.10/4.29      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 4.10/4.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.10/4.29  thf('25', plain,
% 4.10/4.29      ((m1_subset_1 @ sk_B @ 
% 4.10/4.29        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.10/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.29  thf(t3_tops_2, axiom,
% 4.10/4.29    (![A:$i]:
% 4.10/4.29     ( ( l1_struct_0 @ A ) =>
% 4.10/4.29       ( ![B:$i]:
% 4.10/4.29         ( ( m1_subset_1 @
% 4.10/4.29             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.10/4.29           ( ![C:$i]:
% 4.10/4.29             ( ( r1_tarski @ C @ B ) =>
% 4.10/4.29               ( m1_subset_1 @
% 4.10/4.29                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 4.10/4.29  thf('26', plain,
% 4.10/4.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.10/4.29         (~ (m1_subset_1 @ X26 @ 
% 4.10/4.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 4.10/4.29          | (m1_subset_1 @ X28 @ 
% 4.10/4.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 4.10/4.29          | ~ (r1_tarski @ X28 @ X26)
% 4.10/4.29          | ~ (l1_struct_0 @ X27))),
% 4.10/4.29      inference('cnf', [status(esa)], [t3_tops_2])).
% 4.10/4.29  thf('27', plain,
% 4.10/4.29      (![X0 : $i]:
% 4.10/4.29         (~ (l1_struct_0 @ sk_A)
% 4.10/4.29          | ~ (r1_tarski @ X0 @ sk_B)
% 4.10/4.29          | (m1_subset_1 @ X0 @ 
% 4.10/4.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.10/4.29      inference('sup-', [status(thm)], ['25', '26'])).
% 4.10/4.29  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 4.10/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.29  thf('29', plain,
% 4.10/4.29      (![X0 : $i]:
% 4.10/4.29         (~ (r1_tarski @ X0 @ sk_B)
% 4.10/4.29          | (m1_subset_1 @ X0 @ 
% 4.10/4.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.10/4.29      inference('demod', [status(thm)], ['27', '28'])).
% 4.10/4.29  thf('30', plain,
% 4.10/4.29      (![X0 : $i]:
% 4.10/4.29         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 4.10/4.29          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.10/4.29      inference('sup-', [status(thm)], ['24', '29'])).
% 4.10/4.29  thf('31', plain,
% 4.10/4.29      (![X21 : $i, X22 : $i]:
% 4.10/4.29         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 4.10/4.29          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 4.10/4.29      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 4.10/4.29  thf('32', plain,
% 4.10/4.29      (![X0 : $i]:
% 4.10/4.29         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 4.10/4.29           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 4.10/4.29      inference('sup-', [status(thm)], ['30', '31'])).
% 4.10/4.29  thf('33', plain,
% 4.10/4.29      (~ (r1_tarski @ 
% 4.10/4.29          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 4.10/4.29          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 4.10/4.29      inference('demod', [status(thm)], ['23', '32'])).
% 4.10/4.29  thf(commutativity_k2_tarski, axiom,
% 4.10/4.29    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.10/4.29  thf('34', plain,
% 4.10/4.29      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 4.10/4.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.10/4.29  thf(l51_zfmisc_1, axiom,
% 4.10/4.29    (![A:$i,B:$i]:
% 4.10/4.29     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.10/4.29  thf('35', plain,
% 4.10/4.29      (![X11 : $i, X12 : $i]:
% 4.10/4.29         ((k3_tarski @ (k2_tarski @ X11 @ X12)) = (k2_xboole_0 @ X11 @ X12))),
% 4.10/4.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.10/4.29  thf('36', plain,
% 4.10/4.29      (![X0 : $i, X1 : $i]:
% 4.10/4.29         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.10/4.29      inference('sup+', [status(thm)], ['34', '35'])).
% 4.10/4.29  thf('37', plain,
% 4.10/4.29      (![X11 : $i, X12 : $i]:
% 4.10/4.29         ((k3_tarski @ (k2_tarski @ X11 @ X12)) = (k2_xboole_0 @ X11 @ X12))),
% 4.10/4.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.10/4.29  thf('38', plain,
% 4.10/4.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.10/4.29      inference('sup+', [status(thm)], ['36', '37'])).
% 4.10/4.29  thf(t7_xboole_1, axiom,
% 4.10/4.29    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.10/4.29  thf('39', plain,
% 4.10/4.29      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 4.10/4.29      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.10/4.29  thf('40', plain,
% 4.10/4.29      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.10/4.29      inference('sup+', [status(thm)], ['38', '39'])).
% 4.10/4.29  thf('41', plain,
% 4.10/4.29      (![X13 : $i, X14 : $i]:
% 4.10/4.29         ((r1_tarski @ (k3_tarski @ X13) @ (k3_tarski @ X14))
% 4.10/4.29          | ~ (r1_tarski @ X13 @ X14))),
% 4.10/4.29      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 4.10/4.29  thf('42', plain,
% 4.10/4.29      (![X0 : $i, X1 : $i]:
% 4.10/4.29         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 4.10/4.29      inference('sup-', [status(thm)], ['40', '41'])).
% 4.10/4.29  thf(t39_xboole_1, axiom,
% 4.10/4.29    (![A:$i,B:$i]:
% 4.10/4.29     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.10/4.29  thf('43', plain,
% 4.10/4.29      (![X2 : $i, X3 : $i]:
% 4.10/4.29         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 4.10/4.29           = (k2_xboole_0 @ X2 @ X3))),
% 4.10/4.29      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.10/4.29  thf(t96_zfmisc_1, axiom,
% 4.10/4.29    (![A:$i,B:$i]:
% 4.10/4.29     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 4.10/4.29       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 4.10/4.29  thf('44', plain,
% 4.10/4.29      (![X15 : $i, X16 : $i]:
% 4.10/4.29         ((k3_tarski @ (k2_xboole_0 @ X15 @ X16))
% 4.10/4.29           = (k2_xboole_0 @ (k3_tarski @ X15) @ (k3_tarski @ X16)))),
% 4.10/4.29      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 4.10/4.29  thf(t43_xboole_1, axiom,
% 4.10/4.29    (![A:$i,B:$i,C:$i]:
% 4.10/4.29     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 4.10/4.29       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 4.10/4.29  thf('45', plain,
% 4.10/4.29      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.10/4.29         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 4.10/4.29          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 4.10/4.29      inference('cnf', [status(esa)], [t43_xboole_1])).
% 4.10/4.29  thf('46', plain,
% 4.10/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.29         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 4.10/4.29          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 4.10/4.29             (k3_tarski @ X0)))),
% 4.10/4.29      inference('sup-', [status(thm)], ['44', '45'])).
% 4.10/4.29  thf('47', plain,
% 4.10/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.29         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 4.10/4.29          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 4.10/4.29             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 4.10/4.29      inference('sup-', [status(thm)], ['43', '46'])).
% 4.10/4.29  thf('48', plain,
% 4.10/4.29      (![X0 : $i, X1 : $i]:
% 4.10/4.29         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 4.10/4.29          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 4.10/4.29      inference('sup-', [status(thm)], ['42', '47'])).
% 4.10/4.29  thf('49', plain, ($false), inference('demod', [status(thm)], ['33', '48'])).
% 4.10/4.29  
% 4.10/4.29  % SZS output end Refutation
% 4.10/4.29  
% 4.13/4.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
