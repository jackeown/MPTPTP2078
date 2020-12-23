%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dUS35GXqj7

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:08 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   67 (  88 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  560 (1122 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X18: $i,X19: $i] :
      ( ( ( k5_setfam_1 @ X19 @ X18 )
        = ( k3_tarski @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k5_setfam_1 @ X19 @ X18 )
        = ( k3_tarski @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( ( k5_setfam_1 @ X19 @ X18 )
        = ( k3_tarski @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['29','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dUS35GXqj7
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:44:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.55/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.79  % Solved by: fo/fo7.sh
% 0.55/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.79  % done 432 iterations in 0.340s
% 0.55/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.79  % SZS output start Refutation
% 0.55/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.79  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.55/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.79  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.55/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.79  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.55/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.79  thf(t6_tops_2, conjecture,
% 0.55/0.79    (![A:$i]:
% 0.55/0.79     ( ( l1_struct_0 @ A ) =>
% 0.55/0.79       ( ![B:$i]:
% 0.55/0.79         ( ( m1_subset_1 @
% 0.55/0.79             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.79           ( ![C:$i]:
% 0.55/0.79             ( ( m1_subset_1 @
% 0.55/0.79                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.79               ( r1_tarski @
% 0.55/0.79                 ( k7_subset_1 @
% 0.55/0.79                   ( u1_struct_0 @ A ) @ 
% 0.55/0.79                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.55/0.79                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.55/0.79                 ( k5_setfam_1 @
% 0.55/0.79                   ( u1_struct_0 @ A ) @ 
% 0.55/0.79                   ( k7_subset_1 @
% 0.55/0.79                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.55/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.79    (~( ![A:$i]:
% 0.55/0.79        ( ( l1_struct_0 @ A ) =>
% 0.55/0.79          ( ![B:$i]:
% 0.55/0.79            ( ( m1_subset_1 @
% 0.55/0.79                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.79              ( ![C:$i]:
% 0.55/0.79                ( ( m1_subset_1 @
% 0.55/0.79                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.79                  ( r1_tarski @
% 0.55/0.79                    ( k7_subset_1 @
% 0.55/0.79                      ( u1_struct_0 @ A ) @ 
% 0.55/0.79                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.55/0.79                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.55/0.79                    ( k5_setfam_1 @
% 0.55/0.79                      ( u1_struct_0 @ A ) @ 
% 0.55/0.79                      ( k7_subset_1 @
% 0.55/0.79                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.55/0.79    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 0.55/0.79  thf('0', plain,
% 0.55/0.79      (~ (r1_tarski @ 
% 0.55/0.79          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.79           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.55/0.79           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.55/0.79          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.79           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('1', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf(redefinition_k5_setfam_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.79       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.55/0.79  thf('2', plain,
% 0.55/0.79      (![X18 : $i, X19 : $i]:
% 0.55/0.79         (((k5_setfam_1 @ X19 @ X18) = (k3_tarski @ X18))
% 0.55/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.55/0.79  thf('3', plain,
% 0.55/0.79      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.55/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.79  thf('4', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_C @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('5', plain,
% 0.55/0.79      (![X18 : $i, X19 : $i]:
% 0.55/0.79         (((k5_setfam_1 @ X19 @ X18) = (k3_tarski @ X18))
% 0.55/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.55/0.79  thf('6', plain,
% 0.55/0.79      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 0.55/0.79      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.79  thf('7', plain,
% 0.55/0.79      (~ (r1_tarski @ 
% 0.55/0.79          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 0.55/0.79           (k3_tarski @ sk_C)) @ 
% 0.55/0.79          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.79           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 0.55/0.79      inference('demod', [status(thm)], ['0', '3', '6'])).
% 0.55/0.79  thf('8', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf(redefinition_k7_subset_1, axiom,
% 0.55/0.79    (![A:$i,B:$i,C:$i]:
% 0.55/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.79       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.55/0.79  thf('9', plain,
% 0.55/0.79      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.79         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.55/0.79          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.55/0.79  thf('10', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.55/0.79           = (k4_xboole_0 @ sk_B @ X0))),
% 0.55/0.79      inference('sup-', [status(thm)], ['8', '9'])).
% 0.55/0.79  thf('11', plain,
% 0.55/0.79      (~ (r1_tarski @ 
% 0.55/0.79          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 0.55/0.79           (k3_tarski @ sk_C)) @ 
% 0.55/0.79          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.55/0.79      inference('demod', [status(thm)], ['7', '10'])).
% 0.55/0.79  thf('12', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf(dt_k5_setfam_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.79       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.55/0.79  thf('13', plain,
% 0.55/0.79      (![X16 : $i, X17 : $i]:
% 0.55/0.79         ((m1_subset_1 @ (k5_setfam_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.55/0.79          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.55/0.79      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.55/0.79  thf('14', plain,
% 0.55/0.79      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.55/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.79  thf('15', plain,
% 0.55/0.79      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.55/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.79  thf('16', plain,
% 0.55/0.79      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.79      inference('demod', [status(thm)], ['14', '15'])).
% 0.55/0.79  thf('17', plain,
% 0.55/0.79      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.79         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.55/0.79          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.55/0.79  thf('18', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 0.55/0.79           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 0.55/0.79      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.79  thf('19', plain,
% 0.55/0.79      (~ (r1_tarski @ 
% 0.55/0.79          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 0.55/0.79          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.55/0.79      inference('demod', [status(thm)], ['11', '18'])).
% 0.55/0.79  thf(t36_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.79  thf('20', plain,
% 0.55/0.79      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.55/0.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.79  thf('21', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf(t3_tops_2, axiom,
% 0.55/0.79    (![A:$i]:
% 0.55/0.79     ( ( l1_struct_0 @ A ) =>
% 0.55/0.79       ( ![B:$i]:
% 0.55/0.79         ( ( m1_subset_1 @
% 0.55/0.79             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.79           ( ![C:$i]:
% 0.55/0.79             ( ( r1_tarski @ C @ B ) =>
% 0.55/0.79               ( m1_subset_1 @
% 0.55/0.79                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.55/0.79  thf('22', plain,
% 0.55/0.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.79         (~ (m1_subset_1 @ X20 @ 
% 0.55/0.79             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.55/0.79          | (m1_subset_1 @ X22 @ 
% 0.55/0.79             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.55/0.79          | ~ (r1_tarski @ X22 @ X20)
% 0.55/0.79          | ~ (l1_struct_0 @ X21))),
% 0.55/0.79      inference('cnf', [status(esa)], [t3_tops_2])).
% 0.55/0.79  thf('23', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         (~ (l1_struct_0 @ sk_A)
% 0.55/0.79          | ~ (r1_tarski @ X0 @ sk_B)
% 0.55/0.79          | (m1_subset_1 @ X0 @ 
% 0.55/0.79             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['21', '22'])).
% 0.55/0.79  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('25', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         (~ (r1_tarski @ X0 @ sk_B)
% 0.55/0.79          | (m1_subset_1 @ X0 @ 
% 0.55/0.79             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.79      inference('demod', [status(thm)], ['23', '24'])).
% 0.55/0.79  thf('26', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.55/0.79          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['20', '25'])).
% 0.55/0.79  thf('27', plain,
% 0.55/0.79      (![X18 : $i, X19 : $i]:
% 0.55/0.79         (((k5_setfam_1 @ X19 @ X18) = (k3_tarski @ X18))
% 0.55/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.55/0.79  thf('28', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 0.55/0.79           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.55/0.79  thf('29', plain,
% 0.55/0.79      (~ (r1_tarski @ 
% 0.55/0.79          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 0.55/0.79          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.55/0.79      inference('demod', [status(thm)], ['19', '28'])).
% 0.55/0.79  thf(t96_zfmisc_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 0.55/0.79       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.55/0.79  thf('30', plain,
% 0.55/0.79      (![X11 : $i, X12 : $i]:
% 0.55/0.79         ((k3_tarski @ (k2_xboole_0 @ X11 @ X12))
% 0.55/0.79           = (k2_xboole_0 @ (k3_tarski @ X11) @ (k3_tarski @ X12)))),
% 0.55/0.79      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.55/0.79  thf(commutativity_k2_xboole_0, axiom,
% 0.55/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.55/0.79  thf('31', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.79  thf(t7_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.79  thf('32', plain,
% 0.55/0.79      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.55/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.79  thf('33', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.55/0.79      inference('sup+', [status(thm)], ['31', '32'])).
% 0.55/0.79  thf('34', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.79      inference('sup+', [status(thm)], ['30', '33'])).
% 0.55/0.79  thf(t39_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.79  thf('35', plain,
% 0.55/0.79      (![X4 : $i, X5 : $i]:
% 0.55/0.79         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.55/0.79           = (k2_xboole_0 @ X4 @ X5))),
% 0.55/0.79      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.55/0.79  thf('36', plain,
% 0.55/0.79      (![X11 : $i, X12 : $i]:
% 0.55/0.79         ((k3_tarski @ (k2_xboole_0 @ X11 @ X12))
% 0.55/0.79           = (k2_xboole_0 @ (k3_tarski @ X11) @ (k3_tarski @ X12)))),
% 0.55/0.79      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.55/0.79  thf(t43_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i,C:$i]:
% 0.55/0.79     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.55/0.79       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.55/0.79  thf('37', plain,
% 0.55/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.79         ((r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.55/0.79          | ~ (r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.55/0.79      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.55/0.79  thf('38', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.79         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.55/0.79          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 0.55/0.79             (k3_tarski @ X0)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.79  thf('39', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.79         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.55/0.79          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 0.55/0.79             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['35', '38'])).
% 0.55/0.79  thf('40', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 0.55/0.79          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['34', '39'])).
% 0.55/0.79  thf('41', plain, ($false), inference('demod', [status(thm)], ['29', '40'])).
% 0.55/0.79  
% 0.55/0.79  % SZS output end Refutation
% 0.55/0.79  
% 0.64/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
