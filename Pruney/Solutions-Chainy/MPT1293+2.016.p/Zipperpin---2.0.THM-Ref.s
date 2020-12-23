%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jA5hCPzTKr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:08 EST 2020

% Result     : Theorem 6.77s
% Output     : Refutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :   71 (  96 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  575 (1108 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k5_setfam_1 @ X24 @ X23 )
        = ( k3_tarski @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','34'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X16 ) @ ( k3_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X16 ) @ ( k3_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
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
    inference(demod,[status(thm)],['35','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jA5hCPzTKr
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 6.77/7.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.77/7.00  % Solved by: fo/fo7.sh
% 6.77/7.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.77/7.00  % done 4757 iterations in 6.539s
% 6.77/7.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.77/7.00  % SZS output start Refutation
% 6.77/7.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.77/7.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.77/7.00  thf(sk_C_type, type, sk_C: $i).
% 6.77/7.00  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 6.77/7.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.77/7.00  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 6.77/7.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.77/7.00  thf(sk_B_type, type, sk_B: $i).
% 6.77/7.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.77/7.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.77/7.00  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.77/7.00  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 6.77/7.00  thf(sk_A_type, type, sk_A: $i).
% 6.77/7.00  thf(t6_tops_2, conjecture,
% 6.77/7.00    (![A:$i]:
% 6.77/7.00     ( ( l1_struct_0 @ A ) =>
% 6.77/7.00       ( ![B:$i]:
% 6.77/7.00         ( ( m1_subset_1 @
% 6.77/7.00             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.77/7.00           ( ![C:$i]:
% 6.77/7.00             ( ( m1_subset_1 @
% 6.77/7.00                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.77/7.00               ( r1_tarski @
% 6.77/7.00                 ( k7_subset_1 @
% 6.77/7.00                   ( u1_struct_0 @ A ) @ 
% 6.77/7.00                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 6.77/7.00                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 6.77/7.00                 ( k5_setfam_1 @
% 6.77/7.00                   ( u1_struct_0 @ A ) @ 
% 6.77/7.00                   ( k7_subset_1 @
% 6.77/7.00                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 6.77/7.00  thf(zf_stmt_0, negated_conjecture,
% 6.77/7.00    (~( ![A:$i]:
% 6.77/7.00        ( ( l1_struct_0 @ A ) =>
% 6.77/7.00          ( ![B:$i]:
% 6.77/7.00            ( ( m1_subset_1 @
% 6.77/7.00                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.77/7.00              ( ![C:$i]:
% 6.77/7.00                ( ( m1_subset_1 @
% 6.77/7.00                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.77/7.00                  ( r1_tarski @
% 6.77/7.00                    ( k7_subset_1 @
% 6.77/7.00                      ( u1_struct_0 @ A ) @ 
% 6.77/7.00                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 6.77/7.00                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 6.77/7.00                    ( k5_setfam_1 @
% 6.77/7.00                      ( u1_struct_0 @ A ) @ 
% 6.77/7.00                      ( k7_subset_1 @
% 6.77/7.00                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 6.77/7.00    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 6.77/7.00  thf('0', plain,
% 6.77/7.00      (~ (r1_tarski @ 
% 6.77/7.00          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.77/7.00           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.77/7.00           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 6.77/7.00          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 6.77/7.00           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 6.77/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.77/7.00  thf('1', plain,
% 6.77/7.00      ((m1_subset_1 @ sk_B @ 
% 6.77/7.00        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.77/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.77/7.00  thf(redefinition_k5_setfam_1, axiom,
% 6.77/7.00    (![A:$i,B:$i]:
% 6.77/7.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.77/7.00       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 6.77/7.00  thf('2', plain,
% 6.77/7.00      (![X23 : $i, X24 : $i]:
% 6.77/7.00         (((k5_setfam_1 @ X24 @ X23) = (k3_tarski @ X23))
% 6.77/7.00          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 6.77/7.00      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 6.77/7.00  thf('3', plain,
% 6.77/7.00      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 6.77/7.00      inference('sup-', [status(thm)], ['1', '2'])).
% 6.77/7.00  thf('4', plain,
% 6.77/7.00      ((m1_subset_1 @ sk_C @ 
% 6.77/7.00        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.77/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.77/7.00  thf('5', plain,
% 6.77/7.00      (![X23 : $i, X24 : $i]:
% 6.77/7.00         (((k5_setfam_1 @ X24 @ X23) = (k3_tarski @ X23))
% 6.77/7.00          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 6.77/7.00      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 6.77/7.00  thf('6', plain,
% 6.77/7.00      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 6.77/7.00      inference('sup-', [status(thm)], ['4', '5'])).
% 6.77/7.00  thf('7', plain,
% 6.77/7.00      (~ (r1_tarski @ 
% 6.77/7.00          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 6.77/7.00           (k3_tarski @ sk_C)) @ 
% 6.77/7.00          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 6.77/7.00           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 6.77/7.00      inference('demod', [status(thm)], ['0', '3', '6'])).
% 6.77/7.00  thf('8', plain,
% 6.77/7.00      ((m1_subset_1 @ sk_B @ 
% 6.77/7.00        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.77/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.77/7.00  thf(redefinition_k7_subset_1, axiom,
% 6.77/7.00    (![A:$i,B:$i,C:$i]:
% 6.77/7.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.77/7.00       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 6.77/7.00  thf('9', plain,
% 6.77/7.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.77/7.00         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 6.77/7.00          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 6.77/7.00      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.77/7.00  thf('10', plain,
% 6.77/7.00      (![X0 : $i]:
% 6.77/7.00         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 6.77/7.00           = (k4_xboole_0 @ sk_B @ X0))),
% 6.77/7.00      inference('sup-', [status(thm)], ['8', '9'])).
% 6.77/7.00  thf('11', plain,
% 6.77/7.00      (~ (r1_tarski @ 
% 6.77/7.00          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 6.77/7.00           (k3_tarski @ sk_C)) @ 
% 6.77/7.00          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 6.77/7.00      inference('demod', [status(thm)], ['7', '10'])).
% 6.77/7.00  thf('12', plain,
% 6.77/7.00      ((m1_subset_1 @ sk_B @ 
% 6.77/7.00        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.77/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.77/7.00  thf(dt_k5_setfam_1, axiom,
% 6.77/7.00    (![A:$i,B:$i]:
% 6.77/7.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.77/7.00       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.77/7.00  thf('13', plain,
% 6.77/7.00      (![X21 : $i, X22 : $i]:
% 6.77/7.00         ((m1_subset_1 @ (k5_setfam_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 6.77/7.00          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 6.77/7.00      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 6.77/7.00  thf('14', plain,
% 6.77/7.00      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 6.77/7.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.77/7.00      inference('sup-', [status(thm)], ['12', '13'])).
% 6.77/7.00  thf('15', plain,
% 6.77/7.00      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 6.77/7.00      inference('sup-', [status(thm)], ['1', '2'])).
% 6.77/7.00  thf('16', plain,
% 6.77/7.00      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.77/7.00      inference('demod', [status(thm)], ['14', '15'])).
% 6.77/7.00  thf('17', plain,
% 6.77/7.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.77/7.00         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 6.77/7.00          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 6.77/7.00      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.77/7.00  thf('18', plain,
% 6.77/7.00      (![X0 : $i]:
% 6.77/7.00         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 6.77/7.00           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 6.77/7.00      inference('sup-', [status(thm)], ['16', '17'])).
% 6.77/7.00  thf('19', plain,
% 6.77/7.00      (~ (r1_tarski @ 
% 6.77/7.00          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 6.77/7.00          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 6.77/7.00      inference('demod', [status(thm)], ['11', '18'])).
% 6.77/7.00  thf(commutativity_k2_xboole_0, axiom,
% 6.77/7.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 6.77/7.00  thf('20', plain,
% 6.77/7.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.77/7.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.77/7.00  thf(t7_xboole_1, axiom,
% 6.77/7.00    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 6.77/7.00  thf('21', plain,
% 6.77/7.00      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 6.77/7.00      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.77/7.00  thf('22', plain,
% 6.77/7.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 6.77/7.00      inference('sup+', [status(thm)], ['20', '21'])).
% 6.77/7.00  thf('23', plain,
% 6.77/7.00      ((m1_subset_1 @ sk_B @ 
% 6.77/7.00        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.77/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.77/7.00  thf(t3_subset, axiom,
% 6.77/7.00    (![A:$i,B:$i]:
% 6.77/7.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.77/7.00  thf('24', plain,
% 6.77/7.00      (![X25 : $i, X26 : $i]:
% 6.77/7.00         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 6.77/7.00      inference('cnf', [status(esa)], [t3_subset])).
% 6.77/7.00  thf('25', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.77/7.00      inference('sup-', [status(thm)], ['23', '24'])).
% 6.77/7.00  thf(t1_xboole_1, axiom,
% 6.77/7.00    (![A:$i,B:$i,C:$i]:
% 6.77/7.00     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 6.77/7.00       ( r1_tarski @ A @ C ) ))).
% 6.77/7.00  thf('26', plain,
% 6.77/7.00      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.77/7.00         (~ (r1_tarski @ X2 @ X3)
% 6.77/7.00          | ~ (r1_tarski @ X3 @ X4)
% 6.77/7.00          | (r1_tarski @ X2 @ X4))),
% 6.77/7.00      inference('cnf', [status(esa)], [t1_xboole_1])).
% 6.77/7.00  thf('27', plain,
% 6.77/7.00      (![X0 : $i]:
% 6.77/7.00         ((r1_tarski @ sk_B @ X0)
% 6.77/7.00          | ~ (r1_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 6.77/7.00      inference('sup-', [status(thm)], ['25', '26'])).
% 6.77/7.00  thf('28', plain,
% 6.77/7.00      (![X0 : $i]:
% 6.77/7.00         (r1_tarski @ sk_B @ 
% 6.77/7.00          (k2_xboole_0 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.77/7.00      inference('sup-', [status(thm)], ['22', '27'])).
% 6.77/7.00  thf(t43_xboole_1, axiom,
% 6.77/7.00    (![A:$i,B:$i,C:$i]:
% 6.77/7.00     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 6.77/7.00       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 6.77/7.00  thf('29', plain,
% 6.77/7.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.77/7.00         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 6.77/7.00          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 6.77/7.00      inference('cnf', [status(esa)], [t43_xboole_1])).
% 6.77/7.00  thf('30', plain,
% 6.77/7.00      (![X0 : $i]:
% 6.77/7.00         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 6.77/7.00          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.77/7.00      inference('sup-', [status(thm)], ['28', '29'])).
% 6.77/7.00  thf('31', plain,
% 6.77/7.00      (![X25 : $i, X27 : $i]:
% 6.77/7.00         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 6.77/7.00      inference('cnf', [status(esa)], [t3_subset])).
% 6.77/7.00  thf('32', plain,
% 6.77/7.00      (![X0 : $i]:
% 6.77/7.00         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 6.77/7.00          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.77/7.00      inference('sup-', [status(thm)], ['30', '31'])).
% 6.77/7.00  thf('33', plain,
% 6.77/7.00      (![X23 : $i, X24 : $i]:
% 6.77/7.00         (((k5_setfam_1 @ X24 @ X23) = (k3_tarski @ X23))
% 6.77/7.00          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 6.77/7.00      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 6.77/7.00  thf('34', plain,
% 6.77/7.00      (![X0 : $i]:
% 6.77/7.00         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 6.77/7.00           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 6.77/7.00      inference('sup-', [status(thm)], ['32', '33'])).
% 6.77/7.00  thf('35', plain,
% 6.77/7.00      (~ (r1_tarski @ 
% 6.77/7.00          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 6.77/7.00          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 6.77/7.00      inference('demod', [status(thm)], ['19', '34'])).
% 6.77/7.00  thf(t96_zfmisc_1, axiom,
% 6.77/7.00    (![A:$i,B:$i]:
% 6.77/7.00     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 6.77/7.00       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 6.77/7.00  thf('36', plain,
% 6.77/7.00      (![X16 : $i, X17 : $i]:
% 6.77/7.00         ((k3_tarski @ (k2_xboole_0 @ X16 @ X17))
% 6.77/7.00           = (k2_xboole_0 @ (k3_tarski @ X16) @ (k3_tarski @ X17)))),
% 6.77/7.00      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 6.77/7.00  thf('37', plain,
% 6.77/7.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 6.77/7.00      inference('sup+', [status(thm)], ['20', '21'])).
% 6.77/7.00  thf('38', plain,
% 6.77/7.00      (![X0 : $i, X1 : $i]:
% 6.77/7.00         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 6.77/7.00      inference('sup+', [status(thm)], ['36', '37'])).
% 6.77/7.00  thf(t39_xboole_1, axiom,
% 6.77/7.00    (![A:$i,B:$i]:
% 6.77/7.00     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 6.77/7.00  thf('39', plain,
% 6.77/7.00      (![X7 : $i, X8 : $i]:
% 6.77/7.00         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 6.77/7.00           = (k2_xboole_0 @ X7 @ X8))),
% 6.77/7.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 6.77/7.00  thf('40', plain,
% 6.77/7.00      (![X16 : $i, X17 : $i]:
% 6.77/7.00         ((k3_tarski @ (k2_xboole_0 @ X16 @ X17))
% 6.77/7.00           = (k2_xboole_0 @ (k3_tarski @ X16) @ (k3_tarski @ X17)))),
% 6.77/7.00      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 6.77/7.00  thf('41', plain,
% 6.77/7.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.77/7.00         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 6.77/7.00          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 6.77/7.00      inference('cnf', [status(esa)], [t43_xboole_1])).
% 6.77/7.00  thf('42', plain,
% 6.77/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.77/7.00         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 6.77/7.00          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 6.77/7.00             (k3_tarski @ X0)))),
% 6.77/7.00      inference('sup-', [status(thm)], ['40', '41'])).
% 6.77/7.00  thf('43', plain,
% 6.77/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.77/7.00         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 6.77/7.00          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 6.77/7.00             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 6.77/7.00      inference('sup-', [status(thm)], ['39', '42'])).
% 6.77/7.00  thf('44', plain,
% 6.77/7.00      (![X0 : $i, X1 : $i]:
% 6.77/7.00         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 6.77/7.00          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 6.77/7.00      inference('sup-', [status(thm)], ['38', '43'])).
% 6.77/7.00  thf('45', plain, ($false), inference('demod', [status(thm)], ['35', '44'])).
% 6.77/7.00  
% 6.77/7.00  % SZS output end Refutation
% 6.77/7.00  
% 6.77/7.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
