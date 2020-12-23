%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9LJsChm1k7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:08 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   70 (  89 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  550 ( 978 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k5_setfam_1 @ X21 @ X20 )
        = ( k3_tarski @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X12 ) @ ( k3_tarski @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('24',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('25',plain,(
    ! [X16: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('26',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
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
    inference(demod,[status(thm)],['31','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9LJsChm1k7
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.64/1.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.64/1.81  % Solved by: fo/fo7.sh
% 1.64/1.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.81  % done 1513 iterations in 1.359s
% 1.64/1.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.64/1.81  % SZS output start Refutation
% 1.64/1.81  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.64/1.81  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.64/1.81  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.81  thf(sk_C_type, type, sk_C: $i).
% 1.64/1.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.64/1.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.64/1.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.64/1.81  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.64/1.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.64/1.81  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.64/1.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.64/1.81  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.64/1.81  thf(t6_tops_2, conjecture,
% 1.64/1.81    (![A:$i]:
% 1.64/1.81     ( ( l1_struct_0 @ A ) =>
% 1.64/1.81       ( ![B:$i]:
% 1.64/1.81         ( ( m1_subset_1 @
% 1.64/1.81             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.81           ( ![C:$i]:
% 1.64/1.81             ( ( m1_subset_1 @
% 1.64/1.81                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.81               ( r1_tarski @
% 1.64/1.81                 ( k7_subset_1 @
% 1.64/1.81                   ( u1_struct_0 @ A ) @ 
% 1.64/1.81                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.64/1.81                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 1.64/1.81                 ( k5_setfam_1 @
% 1.64/1.81                   ( u1_struct_0 @ A ) @ 
% 1.64/1.81                   ( k7_subset_1 @
% 1.64/1.81                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 1.64/1.81  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.81    (~( ![A:$i]:
% 1.64/1.81        ( ( l1_struct_0 @ A ) =>
% 1.64/1.81          ( ![B:$i]:
% 1.64/1.81            ( ( m1_subset_1 @
% 1.64/1.81                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.81              ( ![C:$i]:
% 1.64/1.81                ( ( m1_subset_1 @
% 1.64/1.81                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.81                  ( r1_tarski @
% 1.64/1.81                    ( k7_subset_1 @
% 1.64/1.81                      ( u1_struct_0 @ A ) @ 
% 1.64/1.81                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.64/1.81                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 1.64/1.81                    ( k5_setfam_1 @
% 1.64/1.81                      ( u1_struct_0 @ A ) @ 
% 1.64/1.81                      ( k7_subset_1 @
% 1.64/1.81                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 1.64/1.81    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 1.64/1.81  thf('0', plain,
% 1.64/1.81      (~ (r1_tarski @ 
% 1.64/1.81          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.81           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.64/1.81           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.64/1.81          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.81           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 1.64/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.81  thf('1', plain,
% 1.64/1.81      ((m1_subset_1 @ sk_B @ 
% 1.64/1.81        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.81  thf(redefinition_k5_setfam_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.64/1.81       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 1.64/1.81  thf('2', plain,
% 1.64/1.81      (![X20 : $i, X21 : $i]:
% 1.64/1.81         (((k5_setfam_1 @ X21 @ X20) = (k3_tarski @ X20))
% 1.64/1.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 1.64/1.81      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.64/1.81  thf('3', plain,
% 1.64/1.81      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 1.64/1.81      inference('sup-', [status(thm)], ['1', '2'])).
% 1.64/1.81  thf('4', plain,
% 1.64/1.81      ((m1_subset_1 @ sk_C @ 
% 1.64/1.81        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.81  thf('5', plain,
% 1.64/1.81      (![X20 : $i, X21 : $i]:
% 1.64/1.81         (((k5_setfam_1 @ X21 @ X20) = (k3_tarski @ X20))
% 1.64/1.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 1.64/1.81      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.64/1.81  thf('6', plain,
% 1.64/1.81      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 1.64/1.81      inference('sup-', [status(thm)], ['4', '5'])).
% 1.64/1.81  thf('7', plain,
% 1.64/1.81      (~ (r1_tarski @ 
% 1.64/1.81          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.64/1.81           (k3_tarski @ sk_C)) @ 
% 1.64/1.81          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.81           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 1.64/1.81      inference('demod', [status(thm)], ['0', '3', '6'])).
% 1.64/1.81  thf('8', plain,
% 1.64/1.81      ((m1_subset_1 @ sk_B @ 
% 1.64/1.81        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.81  thf(redefinition_k7_subset_1, axiom,
% 1.64/1.81    (![A:$i,B:$i,C:$i]:
% 1.64/1.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.81       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.64/1.81  thf('9', plain,
% 1.64/1.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.64/1.81         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.64/1.81          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 1.64/1.81      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.64/1.81  thf('10', plain,
% 1.64/1.81      (![X0 : $i]:
% 1.64/1.81         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 1.64/1.81           = (k4_xboole_0 @ sk_B @ X0))),
% 1.64/1.81      inference('sup-', [status(thm)], ['8', '9'])).
% 1.64/1.81  thf('11', plain,
% 1.64/1.81      (~ (r1_tarski @ 
% 1.64/1.81          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.64/1.81           (k3_tarski @ sk_C)) @ 
% 1.64/1.81          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.64/1.81      inference('demod', [status(thm)], ['7', '10'])).
% 1.64/1.81  thf('12', plain,
% 1.64/1.81      ((m1_subset_1 @ sk_B @ 
% 1.64/1.81        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.81  thf(t3_subset, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.64/1.81  thf('13', plain,
% 1.64/1.81      (![X22 : $i, X23 : $i]:
% 1.64/1.81         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 1.64/1.81      inference('cnf', [status(esa)], [t3_subset])).
% 1.64/1.81  thf('14', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.81      inference('sup-', [status(thm)], ['12', '13'])).
% 1.64/1.81  thf(t109_xboole_1, axiom,
% 1.64/1.81    (![A:$i,B:$i,C:$i]:
% 1.64/1.81     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 1.64/1.81  thf('15', plain,
% 1.64/1.81      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.81         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 1.64/1.81      inference('cnf', [status(esa)], [t109_xboole_1])).
% 1.64/1.81  thf('16', plain,
% 1.64/1.81      (![X0 : $i]:
% 1.64/1.81         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.64/1.81          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.81      inference('sup-', [status(thm)], ['14', '15'])).
% 1.64/1.81  thf('17', plain,
% 1.64/1.81      (![X22 : $i, X24 : $i]:
% 1.64/1.81         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.64/1.81      inference('cnf', [status(esa)], [t3_subset])).
% 1.64/1.81  thf('18', plain,
% 1.64/1.81      (![X0 : $i]:
% 1.64/1.81         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.64/1.81          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.81      inference('sup-', [status(thm)], ['16', '17'])).
% 1.64/1.81  thf('19', plain,
% 1.64/1.81      (![X20 : $i, X21 : $i]:
% 1.64/1.81         (((k5_setfam_1 @ X21 @ X20) = (k3_tarski @ X20))
% 1.64/1.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 1.64/1.81      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.64/1.81  thf('20', plain,
% 1.64/1.81      (![X0 : $i]:
% 1.64/1.81         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 1.64/1.81           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.64/1.81      inference('sup-', [status(thm)], ['18', '19'])).
% 1.64/1.81  thf('21', plain,
% 1.64/1.81      (~ (r1_tarski @ 
% 1.64/1.81          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.64/1.81           (k3_tarski @ sk_C)) @ 
% 1.64/1.81          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.64/1.81      inference('demod', [status(thm)], ['11', '20'])).
% 1.64/1.81  thf('22', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.81      inference('sup-', [status(thm)], ['12', '13'])).
% 1.64/1.81  thf(t95_zfmisc_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( r1_tarski @ A @ B ) =>
% 1.64/1.81       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 1.64/1.81  thf('23', plain,
% 1.64/1.81      (![X12 : $i, X13 : $i]:
% 1.64/1.81         ((r1_tarski @ (k3_tarski @ X12) @ (k3_tarski @ X13))
% 1.64/1.81          | ~ (r1_tarski @ X12 @ X13))),
% 1.64/1.81      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 1.64/1.81  thf('24', plain,
% 1.64/1.81      ((r1_tarski @ (k3_tarski @ sk_B) @ 
% 1.64/1.81        (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.81      inference('sup-', [status(thm)], ['22', '23'])).
% 1.64/1.81  thf(t99_zfmisc_1, axiom,
% 1.64/1.81    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 1.64/1.81  thf('25', plain, (![X16 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X16)) = (X16))),
% 1.64/1.81      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 1.64/1.81  thf('26', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.64/1.81      inference('demod', [status(thm)], ['24', '25'])).
% 1.64/1.81  thf('27', plain,
% 1.64/1.81      (![X22 : $i, X24 : $i]:
% 1.64/1.81         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.64/1.81      inference('cnf', [status(esa)], [t3_subset])).
% 1.64/1.81  thf('28', plain,
% 1.64/1.81      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.81      inference('sup-', [status(thm)], ['26', '27'])).
% 1.64/1.81  thf('29', plain,
% 1.64/1.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.64/1.81         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.64/1.81          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 1.64/1.81      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.64/1.81  thf('30', plain,
% 1.64/1.81      (![X0 : $i]:
% 1.64/1.81         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 1.64/1.81           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 1.64/1.81      inference('sup-', [status(thm)], ['28', '29'])).
% 1.64/1.81  thf('31', plain,
% 1.64/1.81      (~ (r1_tarski @ 
% 1.64/1.81          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 1.64/1.81          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.64/1.81      inference('demod', [status(thm)], ['21', '30'])).
% 1.64/1.81  thf(t96_zfmisc_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 1.64/1.81       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 1.64/1.81  thf('32', plain,
% 1.64/1.81      (![X14 : $i, X15 : $i]:
% 1.64/1.81         ((k3_tarski @ (k2_xboole_0 @ X14 @ X15))
% 1.64/1.81           = (k2_xboole_0 @ (k3_tarski @ X14) @ (k3_tarski @ X15)))),
% 1.64/1.81      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 1.64/1.81  thf(commutativity_k2_xboole_0, axiom,
% 1.64/1.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.64/1.81  thf('33', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.64/1.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.64/1.81  thf(t7_xboole_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.64/1.81  thf('34', plain,
% 1.64/1.81      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 1.64/1.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.64/1.81  thf('35', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.64/1.81      inference('sup+', [status(thm)], ['33', '34'])).
% 1.64/1.81  thf('36', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i]:
% 1.64/1.81         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 1.64/1.81      inference('sup+', [status(thm)], ['32', '35'])).
% 1.64/1.81  thf(t39_xboole_1, axiom,
% 1.64/1.81    (![A:$i,B:$i]:
% 1.64/1.81     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.64/1.81  thf('37', plain,
% 1.64/1.81      (![X5 : $i, X6 : $i]:
% 1.64/1.81         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.64/1.81           = (k2_xboole_0 @ X5 @ X6))),
% 1.64/1.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.64/1.81  thf('38', plain,
% 1.64/1.81      (![X14 : $i, X15 : $i]:
% 1.64/1.81         ((k3_tarski @ (k2_xboole_0 @ X14 @ X15))
% 1.64/1.81           = (k2_xboole_0 @ (k3_tarski @ X14) @ (k3_tarski @ X15)))),
% 1.64/1.81      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 1.64/1.81  thf(t43_xboole_1, axiom,
% 1.64/1.81    (![A:$i,B:$i,C:$i]:
% 1.64/1.81     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.64/1.81       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.64/1.81  thf('39', plain,
% 1.64/1.81      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.64/1.81         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 1.64/1.81          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 1.64/1.81      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.64/1.81  thf('40', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 1.64/1.81          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 1.64/1.81             (k3_tarski @ X0)))),
% 1.64/1.81      inference('sup-', [status(thm)], ['38', '39'])).
% 1.64/1.81  thf('41', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.81         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 1.64/1.81          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 1.64/1.81             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 1.64/1.81      inference('sup-', [status(thm)], ['37', '40'])).
% 1.64/1.81  thf('42', plain,
% 1.64/1.81      (![X0 : $i, X1 : $i]:
% 1.64/1.81         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 1.64/1.81          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 1.64/1.81      inference('sup-', [status(thm)], ['36', '41'])).
% 1.64/1.81  thf('43', plain, ($false), inference('demod', [status(thm)], ['31', '42'])).
% 1.64/1.81  
% 1.64/1.81  % SZS output end Refutation
% 1.64/1.81  
% 1.66/1.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
