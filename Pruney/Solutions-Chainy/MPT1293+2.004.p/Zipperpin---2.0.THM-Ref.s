%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6vB1DXvJ9x

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:07 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   73 (  95 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  599 (1169 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ( ( k5_setfam_1 @ X21 @ X20 )
        = ( k3_tarski @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k5_setfam_1 @ X21 @ X20 )
        = ( k3_tarski @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
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

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('14',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k5_setfam_1 @ X21 @ X20 )
        = ( k3_tarski @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X13 ) @ ( k3_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X13 ) @ ( k3_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['29','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6vB1DXvJ9x
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.61/1.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.61/1.78  % Solved by: fo/fo7.sh
% 1.61/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.78  % done 1134 iterations in 1.328s
% 1.61/1.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.61/1.78  % SZS output start Refutation
% 1.61/1.78  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.61/1.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.61/1.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.61/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.61/1.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.61/1.78  thf(sk_C_type, type, sk_C: $i).
% 1.61/1.78  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.61/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.61/1.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.61/1.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.61/1.78  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.61/1.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.61/1.78  thf(t6_tops_2, conjecture,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( l1_struct_0 @ A ) =>
% 1.61/1.78       ( ![B:$i]:
% 1.61/1.78         ( ( m1_subset_1 @
% 1.61/1.78             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.61/1.78           ( ![C:$i]:
% 1.61/1.78             ( ( m1_subset_1 @
% 1.61/1.78                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.61/1.78               ( r1_tarski @
% 1.61/1.78                 ( k7_subset_1 @
% 1.61/1.78                   ( u1_struct_0 @ A ) @ 
% 1.61/1.78                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.61/1.78                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 1.61/1.78                 ( k5_setfam_1 @
% 1.61/1.78                   ( u1_struct_0 @ A ) @ 
% 1.61/1.78                   ( k7_subset_1 @
% 1.61/1.78                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 1.61/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.78    (~( ![A:$i]:
% 1.61/1.78        ( ( l1_struct_0 @ A ) =>
% 1.61/1.78          ( ![B:$i]:
% 1.61/1.78            ( ( m1_subset_1 @
% 1.61/1.78                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.61/1.78              ( ![C:$i]:
% 1.61/1.78                ( ( m1_subset_1 @
% 1.61/1.78                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.61/1.78                  ( r1_tarski @
% 1.61/1.78                    ( k7_subset_1 @
% 1.61/1.78                      ( u1_struct_0 @ A ) @ 
% 1.61/1.78                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.61/1.78                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 1.61/1.78                    ( k5_setfam_1 @
% 1.61/1.78                      ( u1_struct_0 @ A ) @ 
% 1.61/1.78                      ( k7_subset_1 @
% 1.61/1.78                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 1.61/1.78    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 1.61/1.78  thf('0', plain,
% 1.61/1.78      (~ (r1_tarski @ 
% 1.61/1.78          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.61/1.78           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.61/1.78           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.61/1.78          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.61/1.78           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('1', plain,
% 1.61/1.78      ((m1_subset_1 @ sk_B @ 
% 1.61/1.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf(redefinition_k5_setfam_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.61/1.78       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 1.61/1.78  thf('2', plain,
% 1.61/1.78      (![X20 : $i, X21 : $i]:
% 1.61/1.78         (((k5_setfam_1 @ X21 @ X20) = (k3_tarski @ X20))
% 1.61/1.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 1.61/1.78      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.61/1.78  thf('3', plain,
% 1.61/1.78      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 1.61/1.78      inference('sup-', [status(thm)], ['1', '2'])).
% 1.61/1.78  thf('4', plain,
% 1.61/1.78      ((m1_subset_1 @ sk_C @ 
% 1.61/1.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('5', plain,
% 1.61/1.78      (![X20 : $i, X21 : $i]:
% 1.61/1.78         (((k5_setfam_1 @ X21 @ X20) = (k3_tarski @ X20))
% 1.61/1.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 1.61/1.78      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.61/1.78  thf('6', plain,
% 1.61/1.78      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 1.61/1.78      inference('sup-', [status(thm)], ['4', '5'])).
% 1.61/1.78  thf('7', plain,
% 1.61/1.78      (~ (r1_tarski @ 
% 1.61/1.78          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.61/1.78           (k3_tarski @ sk_C)) @ 
% 1.61/1.78          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.61/1.78           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 1.61/1.78      inference('demod', [status(thm)], ['0', '3', '6'])).
% 1.61/1.78  thf('8', plain,
% 1.61/1.78      ((m1_subset_1 @ sk_B @ 
% 1.61/1.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf(redefinition_k7_subset_1, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.61/1.78       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.61/1.78  thf('9', plain,
% 1.61/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.61/1.78         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 1.61/1.78          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 1.61/1.78      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.61/1.78  thf('10', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 1.61/1.78           = (k4_xboole_0 @ sk_B @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['8', '9'])).
% 1.61/1.78  thf('11', plain,
% 1.61/1.78      (~ (r1_tarski @ 
% 1.61/1.78          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.61/1.78           (k3_tarski @ sk_C)) @ 
% 1.61/1.78          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.61/1.78      inference('demod', [status(thm)], ['7', '10'])).
% 1.61/1.78  thf('12', plain,
% 1.61/1.78      ((m1_subset_1 @ sk_B @ 
% 1.61/1.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf(dt_k5_setfam_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.61/1.78       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.61/1.78  thf('13', plain,
% 1.61/1.78      (![X18 : $i, X19 : $i]:
% 1.61/1.78         ((m1_subset_1 @ (k5_setfam_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 1.61/1.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 1.61/1.78      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 1.61/1.78  thf('14', plain,
% 1.61/1.78      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.61/1.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['12', '13'])).
% 1.61/1.78  thf('15', plain,
% 1.61/1.78      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 1.61/1.78      inference('sup-', [status(thm)], ['1', '2'])).
% 1.61/1.78  thf('16', plain,
% 1.61/1.78      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.61/1.78      inference('demod', [status(thm)], ['14', '15'])).
% 1.61/1.78  thf('17', plain,
% 1.61/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.61/1.78         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 1.61/1.78          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 1.61/1.78      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.61/1.78  thf('18', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 1.61/1.78           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['16', '17'])).
% 1.61/1.78  thf('19', plain,
% 1.61/1.78      (~ (r1_tarski @ 
% 1.61/1.78          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 1.61/1.78          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.61/1.78      inference('demod', [status(thm)], ['11', '18'])).
% 1.61/1.78  thf(t36_xboole_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.61/1.78  thf('20', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.61/1.78      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.61/1.78  thf('21', plain,
% 1.61/1.78      ((m1_subset_1 @ sk_B @ 
% 1.61/1.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf(t3_tops_2, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( l1_struct_0 @ A ) =>
% 1.61/1.78       ( ![B:$i]:
% 1.61/1.78         ( ( m1_subset_1 @
% 1.61/1.78             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.61/1.78           ( ![C:$i]:
% 1.61/1.78             ( ( r1_tarski @ C @ B ) =>
% 1.61/1.78               ( m1_subset_1 @
% 1.61/1.78                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.61/1.78  thf('22', plain,
% 1.61/1.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.61/1.78         (~ (m1_subset_1 @ X22 @ 
% 1.61/1.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 1.61/1.78          | (m1_subset_1 @ X24 @ 
% 1.61/1.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 1.61/1.78          | ~ (r1_tarski @ X24 @ X22)
% 1.61/1.78          | ~ (l1_struct_0 @ X23))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_tops_2])).
% 1.61/1.78  thf('23', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (~ (l1_struct_0 @ sk_A)
% 1.61/1.78          | ~ (r1_tarski @ X0 @ sk_B)
% 1.61/1.78          | (m1_subset_1 @ X0 @ 
% 1.61/1.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.61/1.78  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('25', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (~ (r1_tarski @ X0 @ sk_B)
% 1.61/1.78          | (m1_subset_1 @ X0 @ 
% 1.61/1.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.61/1.78      inference('demod', [status(thm)], ['23', '24'])).
% 1.61/1.78  thf('26', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.61/1.78          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['20', '25'])).
% 1.61/1.78  thf('27', plain,
% 1.61/1.78      (![X20 : $i, X21 : $i]:
% 1.61/1.78         (((k5_setfam_1 @ X21 @ X20) = (k3_tarski @ X20))
% 1.61/1.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 1.61/1.78      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.61/1.78  thf('28', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 1.61/1.78           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['26', '27'])).
% 1.61/1.78  thf('29', plain,
% 1.61/1.78      (~ (r1_tarski @ 
% 1.61/1.78          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 1.61/1.78          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.61/1.78      inference('demod', [status(thm)], ['19', '28'])).
% 1.61/1.78  thf(t96_zfmisc_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 1.61/1.78       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 1.61/1.78  thf('30', plain,
% 1.61/1.78      (![X13 : $i, X14 : $i]:
% 1.61/1.78         ((k3_tarski @ (k2_xboole_0 @ X13 @ X14))
% 1.61/1.78           = (k2_xboole_0 @ (k3_tarski @ X13) @ (k3_tarski @ X14)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 1.61/1.78  thf(commutativity_k2_tarski, axiom,
% 1.61/1.78    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.61/1.78  thf('31', plain,
% 1.61/1.78      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 1.61/1.78      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.61/1.78  thf(l51_zfmisc_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.61/1.78  thf('32', plain,
% 1.61/1.78      (![X11 : $i, X12 : $i]:
% 1.61/1.78         ((k3_tarski @ (k2_tarski @ X11 @ X12)) = (k2_xboole_0 @ X11 @ X12))),
% 1.61/1.78      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.61/1.78  thf('33', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['31', '32'])).
% 1.61/1.78  thf('34', plain,
% 1.61/1.78      (![X11 : $i, X12 : $i]:
% 1.61/1.78         ((k3_tarski @ (k2_tarski @ X11 @ X12)) = (k2_xboole_0 @ X11 @ X12))),
% 1.61/1.78      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.61/1.78  thf('35', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['33', '34'])).
% 1.61/1.78  thf(t7_xboole_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.61/1.78  thf('36', plain,
% 1.61/1.78      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.61/1.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.61/1.78  thf('37', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['35', '36'])).
% 1.61/1.78  thf('38', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['30', '37'])).
% 1.61/1.78  thf(t39_xboole_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.61/1.78  thf('39', plain,
% 1.61/1.78      (![X2 : $i, X3 : $i]:
% 1.61/1.78         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 1.61/1.78           = (k2_xboole_0 @ X2 @ X3))),
% 1.61/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.61/1.78  thf('40', plain,
% 1.61/1.78      (![X13 : $i, X14 : $i]:
% 1.61/1.78         ((k3_tarski @ (k2_xboole_0 @ X13 @ X14))
% 1.61/1.78           = (k2_xboole_0 @ (k3_tarski @ X13) @ (k3_tarski @ X14)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 1.61/1.78  thf(t43_xboole_1, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.61/1.78       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.61/1.78  thf('41', plain,
% 1.61/1.78      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.61/1.78         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 1.61/1.78          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.61/1.78  thf('42', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 1.61/1.78          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 1.61/1.78             (k3_tarski @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['40', '41'])).
% 1.61/1.78  thf('43', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 1.61/1.78          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 1.61/1.78             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['39', '42'])).
% 1.61/1.78  thf('44', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 1.61/1.78          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['38', '43'])).
% 1.61/1.78  thf('45', plain, ($false), inference('demod', [status(thm)], ['29', '44'])).
% 1.61/1.78  
% 1.61/1.78  % SZS output end Refutation
% 1.61/1.78  
% 1.61/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
