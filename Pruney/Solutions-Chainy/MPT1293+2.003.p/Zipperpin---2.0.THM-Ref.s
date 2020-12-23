%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bjloZRQQhN

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:06 EST 2020

% Result     : Theorem 21.23s
% Output     : Refutation 21.23s
% Verified   : 
% Statistics : Number of formulae       :   75 (  96 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  590 (1097 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X23: $i,X24: $i] :
      ( ( ( k5_setfam_1 @ X24 @ X23 )
        = ( k3_tarski @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k5_setfam_1 @ X24 @ X23 )
        = ( k3_tarski @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
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

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k5_setfam_1 @ X24 @ X23 )
        = ( k3_tarski @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','18','29'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X16 ) @ ( k3_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X16 ) @ ( k3_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['30','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bjloZRQQhN
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 21.23/21.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.23/21.41  % Solved by: fo/fo7.sh
% 21.23/21.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.23/21.41  % done 9963 iterations in 20.959s
% 21.23/21.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.23/21.41  % SZS output start Refutation
% 21.23/21.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 21.23/21.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.23/21.41  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 21.23/21.41  thf(sk_C_type, type, sk_C: $i).
% 21.23/21.41  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 21.23/21.41  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 21.23/21.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 21.23/21.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.23/21.41  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 21.23/21.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.23/21.41  thf(sk_B_type, type, sk_B: $i).
% 21.23/21.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 21.23/21.41  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 21.23/21.41  thf(sk_A_type, type, sk_A: $i).
% 21.23/21.41  thf(t6_tops_2, conjecture,
% 21.23/21.42    (![A:$i]:
% 21.23/21.42     ( ( l1_struct_0 @ A ) =>
% 21.23/21.42       ( ![B:$i]:
% 21.23/21.42         ( ( m1_subset_1 @
% 21.23/21.42             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 21.23/21.42           ( ![C:$i]:
% 21.23/21.42             ( ( m1_subset_1 @
% 21.23/21.42                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 21.23/21.42               ( r1_tarski @
% 21.23/21.42                 ( k7_subset_1 @
% 21.23/21.42                   ( u1_struct_0 @ A ) @ 
% 21.23/21.42                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 21.23/21.42                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 21.23/21.42                 ( k5_setfam_1 @
% 21.23/21.42                   ( u1_struct_0 @ A ) @ 
% 21.23/21.42                   ( k7_subset_1 @
% 21.23/21.42                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 21.23/21.42  thf(zf_stmt_0, negated_conjecture,
% 21.23/21.42    (~( ![A:$i]:
% 21.23/21.42        ( ( l1_struct_0 @ A ) =>
% 21.23/21.42          ( ![B:$i]:
% 21.23/21.42            ( ( m1_subset_1 @
% 21.23/21.42                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 21.23/21.42              ( ![C:$i]:
% 21.23/21.42                ( ( m1_subset_1 @
% 21.23/21.42                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 21.23/21.42                  ( r1_tarski @
% 21.23/21.42                    ( k7_subset_1 @
% 21.23/21.42                      ( u1_struct_0 @ A ) @ 
% 21.23/21.42                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 21.23/21.42                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 21.23/21.42                    ( k5_setfam_1 @
% 21.23/21.42                      ( u1_struct_0 @ A ) @ 
% 21.23/21.42                      ( k7_subset_1 @
% 21.23/21.42                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 21.23/21.42    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 21.23/21.42  thf('0', plain,
% 21.23/21.42      (~ (r1_tarski @ 
% 21.23/21.42          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 21.23/21.42           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 21.23/21.42           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 21.23/21.42          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 21.23/21.42           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 21.23/21.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.23/21.42  thf('1', plain,
% 21.23/21.42      ((m1_subset_1 @ sk_B @ 
% 21.23/21.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 21.23/21.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.23/21.42  thf(redefinition_k5_setfam_1, axiom,
% 21.23/21.42    (![A:$i,B:$i]:
% 21.23/21.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 21.23/21.42       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 21.23/21.42  thf('2', plain,
% 21.23/21.42      (![X23 : $i, X24 : $i]:
% 21.23/21.42         (((k5_setfam_1 @ X24 @ X23) = (k3_tarski @ X23))
% 21.23/21.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 21.23/21.42      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 21.23/21.42  thf('3', plain,
% 21.23/21.42      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 21.23/21.42      inference('sup-', [status(thm)], ['1', '2'])).
% 21.23/21.42  thf('4', plain,
% 21.23/21.42      ((m1_subset_1 @ sk_C @ 
% 21.23/21.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 21.23/21.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.23/21.42  thf('5', plain,
% 21.23/21.42      (![X23 : $i, X24 : $i]:
% 21.23/21.42         (((k5_setfam_1 @ X24 @ X23) = (k3_tarski @ X23))
% 21.23/21.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 21.23/21.42      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 21.23/21.42  thf('6', plain,
% 21.23/21.42      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 21.23/21.42      inference('sup-', [status(thm)], ['4', '5'])).
% 21.23/21.42  thf('7', plain,
% 21.23/21.42      (~ (r1_tarski @ 
% 21.23/21.42          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 21.23/21.42           (k3_tarski @ sk_C)) @ 
% 21.23/21.42          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 21.23/21.42           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 21.23/21.42      inference('demod', [status(thm)], ['0', '3', '6'])).
% 21.23/21.42  thf('8', plain,
% 21.23/21.42      ((m1_subset_1 @ sk_B @ 
% 21.23/21.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 21.23/21.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.23/21.42  thf(redefinition_k7_subset_1, axiom,
% 21.23/21.42    (![A:$i,B:$i,C:$i]:
% 21.23/21.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 21.23/21.42       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 21.23/21.42  thf('9', plain,
% 21.23/21.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 21.23/21.42         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 21.23/21.42          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 21.23/21.42      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 21.23/21.42  thf('10', plain,
% 21.23/21.42      (![X0 : $i]:
% 21.23/21.42         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 21.23/21.42           = (k4_xboole_0 @ sk_B @ X0))),
% 21.23/21.42      inference('sup-', [status(thm)], ['8', '9'])).
% 21.23/21.42  thf('11', plain,
% 21.23/21.42      (~ (r1_tarski @ 
% 21.23/21.42          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 21.23/21.42           (k3_tarski @ sk_C)) @ 
% 21.23/21.42          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 21.23/21.42      inference('demod', [status(thm)], ['7', '10'])).
% 21.23/21.42  thf('12', plain,
% 21.23/21.42      ((m1_subset_1 @ sk_B @ 
% 21.23/21.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 21.23/21.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.23/21.42  thf(dt_k5_setfam_1, axiom,
% 21.23/21.42    (![A:$i,B:$i]:
% 21.23/21.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 21.23/21.42       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 21.23/21.42  thf('13', plain,
% 21.23/21.42      (![X21 : $i, X22 : $i]:
% 21.23/21.42         ((m1_subset_1 @ (k5_setfam_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 21.23/21.42          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 21.23/21.42      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 21.23/21.42  thf('14', plain,
% 21.23/21.42      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 21.23/21.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 21.23/21.42      inference('sup-', [status(thm)], ['12', '13'])).
% 21.23/21.42  thf('15', plain,
% 21.23/21.42      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 21.23/21.42      inference('sup-', [status(thm)], ['1', '2'])).
% 21.23/21.42  thf('16', plain,
% 21.23/21.42      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 21.23/21.42      inference('demod', [status(thm)], ['14', '15'])).
% 21.23/21.42  thf('17', plain,
% 21.23/21.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 21.23/21.42         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 21.23/21.42          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 21.23/21.42      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 21.23/21.42  thf('18', plain,
% 21.23/21.42      (![X0 : $i]:
% 21.23/21.42         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 21.23/21.42           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 21.23/21.42      inference('sup-', [status(thm)], ['16', '17'])).
% 21.23/21.42  thf('19', plain,
% 21.23/21.42      ((m1_subset_1 @ sk_B @ 
% 21.23/21.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 21.23/21.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.23/21.42  thf(t3_subset, axiom,
% 21.23/21.42    (![A:$i,B:$i]:
% 21.23/21.42     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 21.23/21.42  thf('20', plain,
% 21.23/21.42      (![X25 : $i, X26 : $i]:
% 21.23/21.42         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 21.23/21.42      inference('cnf', [status(esa)], [t3_subset])).
% 21.23/21.42  thf('21', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 21.23/21.42      inference('sup-', [status(thm)], ['19', '20'])).
% 21.23/21.42  thf(t36_xboole_1, axiom,
% 21.23/21.42    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 21.23/21.42  thf('22', plain,
% 21.23/21.42      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 21.23/21.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 21.23/21.42  thf(t1_xboole_1, axiom,
% 21.23/21.42    (![A:$i,B:$i,C:$i]:
% 21.23/21.42     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 21.23/21.42       ( r1_tarski @ A @ C ) ))).
% 21.23/21.42  thf('23', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.23/21.42         (~ (r1_tarski @ X0 @ X1)
% 21.23/21.42          | ~ (r1_tarski @ X1 @ X2)
% 21.23/21.42          | (r1_tarski @ X0 @ X2))),
% 21.23/21.42      inference('cnf', [status(esa)], [t1_xboole_1])).
% 21.23/21.42  thf('24', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.23/21.42         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 21.23/21.42      inference('sup-', [status(thm)], ['22', '23'])).
% 21.23/21.42  thf('25', plain,
% 21.23/21.42      (![X0 : $i]:
% 21.23/21.42         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 21.23/21.42          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 21.23/21.42      inference('sup-', [status(thm)], ['21', '24'])).
% 21.23/21.42  thf('26', plain,
% 21.23/21.42      (![X25 : $i, X27 : $i]:
% 21.23/21.42         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 21.23/21.42      inference('cnf', [status(esa)], [t3_subset])).
% 21.23/21.42  thf('27', plain,
% 21.23/21.42      (![X0 : $i]:
% 21.23/21.42         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 21.23/21.42          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 21.23/21.42      inference('sup-', [status(thm)], ['25', '26'])).
% 21.23/21.42  thf('28', plain,
% 21.23/21.42      (![X23 : $i, X24 : $i]:
% 21.23/21.42         (((k5_setfam_1 @ X24 @ X23) = (k3_tarski @ X23))
% 21.23/21.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 21.23/21.42      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 21.23/21.42  thf('29', plain,
% 21.23/21.42      (![X0 : $i]:
% 21.23/21.42         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 21.23/21.42           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 21.23/21.42      inference('sup-', [status(thm)], ['27', '28'])).
% 21.23/21.42  thf('30', plain,
% 21.23/21.42      (~ (r1_tarski @ 
% 21.23/21.42          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 21.23/21.42          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 21.23/21.42      inference('demod', [status(thm)], ['11', '18', '29'])).
% 21.23/21.42  thf(t96_zfmisc_1, axiom,
% 21.23/21.42    (![A:$i,B:$i]:
% 21.23/21.42     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 21.23/21.42       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 21.23/21.42  thf('31', plain,
% 21.23/21.42      (![X16 : $i, X17 : $i]:
% 21.23/21.42         ((k3_tarski @ (k2_xboole_0 @ X16 @ X17))
% 21.23/21.42           = (k2_xboole_0 @ (k3_tarski @ X16) @ (k3_tarski @ X17)))),
% 21.23/21.42      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 21.23/21.42  thf(commutativity_k2_tarski, axiom,
% 21.23/21.42    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 21.23/21.42  thf('32', plain,
% 21.23/21.42      (![X12 : $i, X13 : $i]:
% 21.23/21.42         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 21.23/21.42      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 21.23/21.42  thf(l51_zfmisc_1, axiom,
% 21.23/21.42    (![A:$i,B:$i]:
% 21.23/21.42     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 21.23/21.42  thf('33', plain,
% 21.23/21.42      (![X14 : $i, X15 : $i]:
% 21.23/21.42         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 21.23/21.42      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 21.23/21.42  thf('34', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i]:
% 21.23/21.42         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 21.23/21.42      inference('sup+', [status(thm)], ['32', '33'])).
% 21.23/21.42  thf('35', plain,
% 21.23/21.42      (![X14 : $i, X15 : $i]:
% 21.23/21.42         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 21.23/21.42      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 21.23/21.42  thf('36', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 21.23/21.42      inference('sup+', [status(thm)], ['34', '35'])).
% 21.23/21.42  thf(t7_xboole_1, axiom,
% 21.23/21.42    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 21.23/21.42  thf('37', plain,
% 21.23/21.42      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 21.23/21.42      inference('cnf', [status(esa)], [t7_xboole_1])).
% 21.23/21.42  thf('38', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 21.23/21.42      inference('sup+', [status(thm)], ['36', '37'])).
% 21.23/21.42  thf('39', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i]:
% 21.23/21.42         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 21.23/21.42      inference('sup+', [status(thm)], ['31', '38'])).
% 21.23/21.42  thf(t39_xboole_1, axiom,
% 21.23/21.42    (![A:$i,B:$i]:
% 21.23/21.42     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 21.23/21.42  thf('40', plain,
% 21.23/21.42      (![X5 : $i, X6 : $i]:
% 21.23/21.42         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 21.23/21.42           = (k2_xboole_0 @ X5 @ X6))),
% 21.23/21.42      inference('cnf', [status(esa)], [t39_xboole_1])).
% 21.23/21.42  thf('41', plain,
% 21.23/21.42      (![X16 : $i, X17 : $i]:
% 21.23/21.42         ((k3_tarski @ (k2_xboole_0 @ X16 @ X17))
% 21.23/21.42           = (k2_xboole_0 @ (k3_tarski @ X16) @ (k3_tarski @ X17)))),
% 21.23/21.42      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 21.23/21.42  thf(t43_xboole_1, axiom,
% 21.23/21.42    (![A:$i,B:$i,C:$i]:
% 21.23/21.42     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 21.23/21.42       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 21.23/21.42  thf('42', plain,
% 21.23/21.42      (![X7 : $i, X8 : $i, X9 : $i]:
% 21.23/21.42         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 21.23/21.42          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 21.23/21.42      inference('cnf', [status(esa)], [t43_xboole_1])).
% 21.23/21.42  thf('43', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.23/21.42         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 21.23/21.42          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 21.23/21.42             (k3_tarski @ X0)))),
% 21.23/21.42      inference('sup-', [status(thm)], ['41', '42'])).
% 21.23/21.42  thf('44', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.23/21.42         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 21.23/21.42          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 21.23/21.42             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 21.23/21.42      inference('sup-', [status(thm)], ['40', '43'])).
% 21.23/21.42  thf('45', plain,
% 21.23/21.42      (![X0 : $i, X1 : $i]:
% 21.23/21.42         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 21.23/21.42          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 21.23/21.42      inference('sup-', [status(thm)], ['39', '44'])).
% 21.23/21.42  thf('46', plain, ($false), inference('demod', [status(thm)], ['30', '45'])).
% 21.23/21.42  
% 21.23/21.42  % SZS output end Refutation
% 21.23/21.42  
% 21.23/21.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
