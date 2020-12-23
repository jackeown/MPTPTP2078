%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NcNlBCePoz

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:06 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   70 (  95 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  576 (1176 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k5_setfam_1 @ X22 @ X21 )
        = ( k3_tarski @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['27','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NcNlBCePoz
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.93/2.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.93/2.13  % Solved by: fo/fo7.sh
% 1.93/2.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.13  % done 1266 iterations in 1.653s
% 1.93/2.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.93/2.13  % SZS output start Refutation
% 1.93/2.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.93/2.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.93/2.13  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.13  thf(sk_C_type, type, sk_C: $i).
% 1.93/2.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.93/2.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.93/2.13  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.93/2.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.93/2.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.93/2.13  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.13  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.93/2.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.93/2.13  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.93/2.13  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.93/2.13  thf(t6_tops_2, conjecture,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( l1_struct_0 @ A ) =>
% 1.93/2.13       ( ![B:$i]:
% 1.93/2.13         ( ( m1_subset_1 @
% 1.93/2.13             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.93/2.13           ( ![C:$i]:
% 1.93/2.13             ( ( m1_subset_1 @
% 1.93/2.13                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.93/2.13               ( r1_tarski @
% 1.93/2.13                 ( k7_subset_1 @
% 1.93/2.13                   ( u1_struct_0 @ A ) @ 
% 1.93/2.13                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.93/2.13                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 1.93/2.13                 ( k5_setfam_1 @
% 1.93/2.13                   ( u1_struct_0 @ A ) @ 
% 1.93/2.13                   ( k7_subset_1 @
% 1.93/2.13                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 1.93/2.13  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.13    (~( ![A:$i]:
% 1.93/2.13        ( ( l1_struct_0 @ A ) =>
% 1.93/2.13          ( ![B:$i]:
% 1.93/2.13            ( ( m1_subset_1 @
% 1.93/2.13                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.93/2.13              ( ![C:$i]:
% 1.93/2.13                ( ( m1_subset_1 @
% 1.93/2.13                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.93/2.13                  ( r1_tarski @
% 1.93/2.13                    ( k7_subset_1 @
% 1.93/2.13                      ( u1_struct_0 @ A ) @ 
% 1.93/2.13                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.93/2.13                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 1.93/2.13                    ( k5_setfam_1 @
% 1.93/2.13                      ( u1_struct_0 @ A ) @ 
% 1.93/2.13                      ( k7_subset_1 @
% 1.93/2.13                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 1.93/2.13    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 1.93/2.13  thf('0', plain,
% 1.93/2.13      (~ (r1_tarski @ 
% 1.93/2.13          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.13           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.93/2.13           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.93/2.13          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.13           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('1', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_B @ 
% 1.93/2.13        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(redefinition_k5_setfam_1, axiom,
% 1.93/2.13    (![A:$i,B:$i]:
% 1.93/2.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.93/2.13       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 1.93/2.13  thf('2', plain,
% 1.93/2.13      (![X21 : $i, X22 : $i]:
% 1.93/2.13         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 1.93/2.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 1.93/2.13      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.93/2.13  thf('3', plain,
% 1.93/2.13      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 1.93/2.13      inference('sup-', [status(thm)], ['1', '2'])).
% 1.93/2.13  thf('4', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_C @ 
% 1.93/2.13        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('5', plain,
% 1.93/2.13      (![X21 : $i, X22 : $i]:
% 1.93/2.13         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 1.93/2.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 1.93/2.13      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.93/2.13  thf('6', plain,
% 1.93/2.13      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 1.93/2.13      inference('sup-', [status(thm)], ['4', '5'])).
% 1.93/2.13  thf('7', plain,
% 1.93/2.13      (~ (r1_tarski @ 
% 1.93/2.13          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.93/2.13           (k3_tarski @ sk_C)) @ 
% 1.93/2.13          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.13           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 1.93/2.13      inference('demod', [status(thm)], ['0', '3', '6'])).
% 1.93/2.13  thf('8', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_B @ 
% 1.93/2.13        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(redefinition_k7_subset_1, axiom,
% 1.93/2.13    (![A:$i,B:$i,C:$i]:
% 1.93/2.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.93/2.13       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.93/2.13  thf('9', plain,
% 1.93/2.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.93/2.13         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.93/2.13          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 1.93/2.13      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.93/2.13  thf('10', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 1.93/2.13           = (k4_xboole_0 @ sk_B @ X0))),
% 1.93/2.13      inference('sup-', [status(thm)], ['8', '9'])).
% 1.93/2.13  thf('11', plain,
% 1.93/2.13      (~ (r1_tarski @ 
% 1.93/2.13          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.93/2.13           (k3_tarski @ sk_C)) @ 
% 1.93/2.13          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.93/2.13      inference('demod', [status(thm)], ['7', '10'])).
% 1.93/2.13  thf('12', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_B @ 
% 1.93/2.13        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(dt_k5_setfam_1, axiom,
% 1.93/2.13    (![A:$i,B:$i]:
% 1.93/2.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.93/2.13       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.93/2.13  thf('13', plain,
% 1.93/2.13      (![X19 : $i, X20 : $i]:
% 1.93/2.13         ((m1_subset_1 @ (k5_setfam_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 1.93/2.13          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 1.93/2.13      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 1.93/2.13  thf('14', plain,
% 1.93/2.13      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.93/2.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.93/2.13      inference('sup-', [status(thm)], ['12', '13'])).
% 1.93/2.13  thf('15', plain,
% 1.93/2.13      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 1.93/2.13      inference('sup-', [status(thm)], ['1', '2'])).
% 1.93/2.13  thf('16', plain,
% 1.93/2.13      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.93/2.13      inference('demod', [status(thm)], ['14', '15'])).
% 1.93/2.13  thf('17', plain,
% 1.93/2.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.93/2.13         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.93/2.13          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 1.93/2.13      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.93/2.13  thf('18', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 1.93/2.13           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 1.93/2.13      inference('sup-', [status(thm)], ['16', '17'])).
% 1.93/2.13  thf('19', plain,
% 1.93/2.13      (~ (r1_tarski @ 
% 1.93/2.13          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 1.93/2.13          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.93/2.13      inference('demod', [status(thm)], ['11', '18'])).
% 1.93/2.13  thf('20', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_B @ 
% 1.93/2.13        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(dt_k7_subset_1, axiom,
% 1.93/2.13    (![A:$i,B:$i,C:$i]:
% 1.93/2.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.93/2.13       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.93/2.13  thf('21', plain,
% 1.93/2.13      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.93/2.13         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.93/2.13          | (m1_subset_1 @ (k7_subset_1 @ X14 @ X13 @ X15) @ 
% 1.93/2.13             (k1_zfmisc_1 @ X14)))),
% 1.93/2.13      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.93/2.13  thf('22', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (m1_subset_1 @ 
% 1.93/2.13          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 1.93/2.13          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.93/2.13      inference('sup-', [status(thm)], ['20', '21'])).
% 1.93/2.13  thf('23', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 1.93/2.13           = (k4_xboole_0 @ sk_B @ X0))),
% 1.93/2.13      inference('sup-', [status(thm)], ['8', '9'])).
% 1.93/2.13  thf('24', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.93/2.13          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.93/2.13      inference('demod', [status(thm)], ['22', '23'])).
% 1.93/2.13  thf('25', plain,
% 1.93/2.13      (![X21 : $i, X22 : $i]:
% 1.93/2.13         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 1.93/2.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 1.93/2.13      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.93/2.13  thf('26', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 1.93/2.13           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.93/2.13      inference('sup-', [status(thm)], ['24', '25'])).
% 1.93/2.13  thf('27', plain,
% 1.93/2.13      (~ (r1_tarski @ 
% 1.93/2.13          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 1.93/2.13          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.93/2.13      inference('demod', [status(thm)], ['19', '26'])).
% 1.93/2.13  thf(t96_zfmisc_1, axiom,
% 1.93/2.13    (![A:$i,B:$i]:
% 1.93/2.13     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 1.93/2.13       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 1.93/2.13  thf('28', plain,
% 1.93/2.13      (![X11 : $i, X12 : $i]:
% 1.93/2.13         ((k3_tarski @ (k2_xboole_0 @ X11 @ X12))
% 1.93/2.13           = (k2_xboole_0 @ (k3_tarski @ X11) @ (k3_tarski @ X12)))),
% 1.93/2.13      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 1.93/2.13  thf(commutativity_k2_tarski, axiom,
% 1.93/2.13    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.93/2.13  thf('29', plain,
% 1.93/2.13      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 1.93/2.13      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.93/2.13  thf(l51_zfmisc_1, axiom,
% 1.93/2.13    (![A:$i,B:$i]:
% 1.93/2.13     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.93/2.13  thf('30', plain,
% 1.93/2.13      (![X9 : $i, X10 : $i]:
% 1.93/2.13         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 1.93/2.13      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.93/2.13  thf('31', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i]:
% 1.93/2.13         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.93/2.13      inference('sup+', [status(thm)], ['29', '30'])).
% 1.93/2.13  thf('32', plain,
% 1.93/2.13      (![X9 : $i, X10 : $i]:
% 1.93/2.13         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 1.93/2.13      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.93/2.13  thf('33', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.93/2.13      inference('sup+', [status(thm)], ['31', '32'])).
% 1.93/2.13  thf(t7_xboole_1, axiom,
% 1.93/2.13    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.93/2.13  thf('34', plain,
% 1.93/2.13      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 1.93/2.13      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.93/2.13  thf('35', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.93/2.13      inference('sup+', [status(thm)], ['33', '34'])).
% 1.93/2.13  thf('36', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i]:
% 1.93/2.13         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 1.93/2.13      inference('sup+', [status(thm)], ['28', '35'])).
% 1.93/2.13  thf(t39_xboole_1, axiom,
% 1.93/2.13    (![A:$i,B:$i]:
% 1.93/2.13     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.93/2.13  thf('37', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i]:
% 1.93/2.13         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.93/2.13           = (k2_xboole_0 @ X0 @ X1))),
% 1.93/2.13      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.93/2.13  thf('38', plain,
% 1.93/2.13      (![X11 : $i, X12 : $i]:
% 1.93/2.13         ((k3_tarski @ (k2_xboole_0 @ X11 @ X12))
% 1.93/2.13           = (k2_xboole_0 @ (k3_tarski @ X11) @ (k3_tarski @ X12)))),
% 1.93/2.13      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 1.93/2.13  thf(t43_xboole_1, axiom,
% 1.93/2.13    (![A:$i,B:$i,C:$i]:
% 1.93/2.13     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.93/2.13       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.93/2.13  thf('39', plain,
% 1.93/2.13      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.93/2.13         ((r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 1.93/2.13          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 1.93/2.13      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.93/2.13  thf('40', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.13         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 1.93/2.13          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 1.93/2.13             (k3_tarski @ X0)))),
% 1.93/2.13      inference('sup-', [status(thm)], ['38', '39'])).
% 1.93/2.13  thf('41', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.13         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 1.93/2.13          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 1.93/2.13             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 1.93/2.13      inference('sup-', [status(thm)], ['37', '40'])).
% 1.93/2.13  thf('42', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i]:
% 1.93/2.13         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 1.93/2.13          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 1.93/2.13      inference('sup-', [status(thm)], ['36', '41'])).
% 1.93/2.13  thf('43', plain, ($false), inference('demod', [status(thm)], ['27', '42'])).
% 1.93/2.13  
% 1.93/2.13  % SZS output end Refutation
% 1.93/2.13  
% 1.93/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
