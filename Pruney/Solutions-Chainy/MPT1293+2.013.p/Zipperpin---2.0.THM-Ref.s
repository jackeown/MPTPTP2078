%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1YX8JVtU1E

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:08 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   64 (  88 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  537 (1129 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['27','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1YX8JVtU1E
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.83  % Solved by: fo/fo7.sh
% 0.64/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.83  % done 413 iterations in 0.371s
% 0.64/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.83  % SZS output start Refutation
% 0.64/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.64/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.64/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.64/0.83  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.64/0.83  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.64/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.64/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.83  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.64/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.83  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.64/0.83  thf(t6_tops_2, conjecture,
% 0.64/0.83    (![A:$i]:
% 0.64/0.83     ( ( l1_struct_0 @ A ) =>
% 0.64/0.83       ( ![B:$i]:
% 0.64/0.83         ( ( m1_subset_1 @
% 0.64/0.83             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.64/0.83           ( ![C:$i]:
% 0.64/0.83             ( ( m1_subset_1 @
% 0.64/0.83                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.64/0.83               ( r1_tarski @
% 0.64/0.83                 ( k7_subset_1 @
% 0.64/0.83                   ( u1_struct_0 @ A ) @ 
% 0.64/0.83                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.64/0.83                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.64/0.83                 ( k5_setfam_1 @
% 0.64/0.83                   ( u1_struct_0 @ A ) @ 
% 0.64/0.83                   ( k7_subset_1 @
% 0.64/0.83                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.64/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.83    (~( ![A:$i]:
% 0.64/0.83        ( ( l1_struct_0 @ A ) =>
% 0.64/0.83          ( ![B:$i]:
% 0.64/0.83            ( ( m1_subset_1 @
% 0.64/0.83                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.64/0.83              ( ![C:$i]:
% 0.64/0.83                ( ( m1_subset_1 @
% 0.64/0.83                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.64/0.83                  ( r1_tarski @
% 0.64/0.83                    ( k7_subset_1 @
% 0.64/0.83                      ( u1_struct_0 @ A ) @ 
% 0.64/0.83                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.64/0.83                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.64/0.83                    ( k5_setfam_1 @
% 0.64/0.83                      ( u1_struct_0 @ A ) @ 
% 0.64/0.83                      ( k7_subset_1 @
% 0.64/0.83                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.64/0.83    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 0.64/0.83  thf('0', plain,
% 0.64/0.83      (~ (r1_tarski @ 
% 0.64/0.83          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.64/0.83           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.64/0.83           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.64/0.83          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.64/0.83           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('1', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_B @ 
% 0.64/0.83        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(redefinition_k5_setfam_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.64/0.83       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.64/0.83  thf('2', plain,
% 0.64/0.83      (![X21 : $i, X22 : $i]:
% 0.64/0.83         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 0.64/0.83          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.64/0.83      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.64/0.83  thf('3', plain,
% 0.64/0.83      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.64/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.64/0.83  thf('4', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_C @ 
% 0.64/0.83        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('5', plain,
% 0.64/0.83      (![X21 : $i, X22 : $i]:
% 0.64/0.83         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 0.64/0.83          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.64/0.83      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.64/0.83  thf('6', plain,
% 0.64/0.83      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 0.64/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.64/0.83  thf('7', plain,
% 0.64/0.83      (~ (r1_tarski @ 
% 0.64/0.83          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 0.64/0.83           (k3_tarski @ sk_C)) @ 
% 0.64/0.83          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.64/0.83           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 0.64/0.83      inference('demod', [status(thm)], ['0', '3', '6'])).
% 0.64/0.83  thf('8', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_B @ 
% 0.64/0.83        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(redefinition_k7_subset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.83       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.64/0.83  thf('9', plain,
% 0.64/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.64/0.83          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.64/0.83      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.64/0.83  thf('10', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.64/0.83           = (k4_xboole_0 @ sk_B @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['8', '9'])).
% 0.64/0.83  thf('11', plain,
% 0.64/0.83      (~ (r1_tarski @ 
% 0.64/0.83          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 0.64/0.83           (k3_tarski @ sk_C)) @ 
% 0.64/0.83          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.64/0.83      inference('demod', [status(thm)], ['7', '10'])).
% 0.64/0.83  thf('12', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_B @ 
% 0.64/0.83        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(dt_k5_setfam_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.64/0.83       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.64/0.83  thf('13', plain,
% 0.64/0.83      (![X19 : $i, X20 : $i]:
% 0.64/0.83         ((m1_subset_1 @ (k5_setfam_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.64/0.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.64/0.83      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.64/0.83  thf('14', plain,
% 0.64/0.83      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.64/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['12', '13'])).
% 0.64/0.83  thf('15', plain,
% 0.64/0.83      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.64/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.64/0.83  thf('16', plain,
% 0.64/0.83      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.83      inference('demod', [status(thm)], ['14', '15'])).
% 0.64/0.83  thf('17', plain,
% 0.64/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.64/0.83          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.64/0.83      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.64/0.83  thf('18', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 0.64/0.83           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.64/0.83  thf('19', plain,
% 0.64/0.83      (~ (r1_tarski @ 
% 0.64/0.83          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 0.64/0.83          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.64/0.83      inference('demod', [status(thm)], ['11', '18'])).
% 0.64/0.83  thf('20', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_B @ 
% 0.64/0.83        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(dt_k7_subset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.83       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.64/0.83  thf('21', plain,
% 0.64/0.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.64/0.83          | (m1_subset_1 @ (k7_subset_1 @ X14 @ X13 @ X15) @ 
% 0.64/0.83             (k1_zfmisc_1 @ X14)))),
% 0.64/0.83      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.64/0.83  thf('22', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (m1_subset_1 @ 
% 0.64/0.83          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 0.64/0.83          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.64/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.64/0.83  thf('23', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.64/0.83           = (k4_xboole_0 @ sk_B @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['8', '9'])).
% 0.64/0.83  thf('24', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.64/0.83          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.64/0.83      inference('demod', [status(thm)], ['22', '23'])).
% 0.64/0.83  thf('25', plain,
% 0.64/0.83      (![X21 : $i, X22 : $i]:
% 0.64/0.83         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 0.64/0.83          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.64/0.83      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.64/0.83  thf('26', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 0.64/0.83           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['24', '25'])).
% 0.64/0.83  thf('27', plain,
% 0.64/0.83      (~ (r1_tarski @ 
% 0.64/0.83          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 0.64/0.83          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.64/0.83      inference('demod', [status(thm)], ['19', '26'])).
% 0.64/0.83  thf(t96_zfmisc_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 0.64/0.83       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.64/0.83  thf('28', plain,
% 0.64/0.83      (![X11 : $i, X12 : $i]:
% 0.64/0.83         ((k3_tarski @ (k2_xboole_0 @ X11 @ X12))
% 0.64/0.83           = (k2_xboole_0 @ (k3_tarski @ X11) @ (k3_tarski @ X12)))),
% 0.64/0.83      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.64/0.83  thf(commutativity_k2_xboole_0, axiom,
% 0.64/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.64/0.83  thf('29', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.64/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.64/0.83  thf(t7_xboole_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.64/0.83  thf('30', plain,
% 0.64/0.83      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.64/0.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.64/0.83  thf('31', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.64/0.83      inference('sup+', [status(thm)], ['29', '30'])).
% 0.64/0.83  thf('32', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 0.64/0.83      inference('sup+', [status(thm)], ['28', '31'])).
% 0.64/0.83  thf(t39_xboole_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.64/0.83  thf('33', plain,
% 0.64/0.83      (![X2 : $i, X3 : $i]:
% 0.64/0.83         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.64/0.83           = (k2_xboole_0 @ X2 @ X3))),
% 0.64/0.83      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.64/0.83  thf('34', plain,
% 0.64/0.83      (![X11 : $i, X12 : $i]:
% 0.64/0.83         ((k3_tarski @ (k2_xboole_0 @ X11 @ X12))
% 0.64/0.83           = (k2_xboole_0 @ (k3_tarski @ X11) @ (k3_tarski @ X12)))),
% 0.64/0.83      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.64/0.83  thf(t43_xboole_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.64/0.83       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.64/0.83  thf('35', plain,
% 0.64/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.83         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.64/0.83          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.64/0.83      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.64/0.83  thf('36', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.83         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.64/0.83          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 0.64/0.83             (k3_tarski @ X0)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.64/0.83  thf('37', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.83         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.64/0.83          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 0.64/0.83             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 0.64/0.83      inference('sup-', [status(thm)], ['33', '36'])).
% 0.64/0.83  thf('38', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 0.64/0.83          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['32', '37'])).
% 0.64/0.83  thf('39', plain, ($false), inference('demod', [status(thm)], ['27', '38'])).
% 0.64/0.83  
% 0.64/0.83  % SZS output end Refutation
% 0.64/0.83  
% 0.64/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
