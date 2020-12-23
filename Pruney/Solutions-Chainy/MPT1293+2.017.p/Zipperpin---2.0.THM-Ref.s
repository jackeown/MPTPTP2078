%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ZZo1qDyON

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:08 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   67 (  87 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  543 (1042 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X19: $i,X20: $i] :
      ( ( ( k5_setfam_1 @ X20 @ X19 )
        = ( k3_tarski @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k5_setfam_1 @ X20 @ X19 )
        = ( k3_tarski @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
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
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k5_setfam_1 @ X20 @ X19 )
        = ( k3_tarski @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('24',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('26',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X12 ) @ ( k3_tarski @ X13 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X12 ) @ ( k3_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ZZo1qDyON
% 0.13/0.37  % Computer   : n018.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:30:42 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.75/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.92  % Solved by: fo/fo7.sh
% 0.75/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.92  % done 848 iterations in 0.482s
% 0.75/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.92  % SZS output start Refutation
% 0.75/0.92  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.75/0.92  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.75/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.92  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.75/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.92  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.75/0.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.92  thf(t6_tops_2, conjecture,
% 0.75/0.92    (![A:$i]:
% 0.75/0.92     ( ( l1_struct_0 @ A ) =>
% 0.75/0.92       ( ![B:$i]:
% 0.75/0.92         ( ( m1_subset_1 @
% 0.75/0.92             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.75/0.92           ( ![C:$i]:
% 0.75/0.92             ( ( m1_subset_1 @
% 0.75/0.92                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.75/0.92               ( r1_tarski @
% 0.75/0.92                 ( k7_subset_1 @
% 0.75/0.92                   ( u1_struct_0 @ A ) @ 
% 0.75/0.92                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.75/0.92                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.75/0.92                 ( k5_setfam_1 @
% 0.75/0.92                   ( u1_struct_0 @ A ) @ 
% 0.75/0.92                   ( k7_subset_1 @
% 0.75/0.92                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.75/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.92    (~( ![A:$i]:
% 0.75/0.92        ( ( l1_struct_0 @ A ) =>
% 0.75/0.92          ( ![B:$i]:
% 0.75/0.92            ( ( m1_subset_1 @
% 0.75/0.92                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.75/0.92              ( ![C:$i]:
% 0.75/0.92                ( ( m1_subset_1 @
% 0.75/0.92                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.75/0.92                  ( r1_tarski @
% 0.75/0.92                    ( k7_subset_1 @
% 0.75/0.92                      ( u1_struct_0 @ A ) @ 
% 0.75/0.92                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.75/0.92                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.75/0.92                    ( k5_setfam_1 @
% 0.75/0.92                      ( u1_struct_0 @ A ) @ 
% 0.75/0.92                      ( k7_subset_1 @
% 0.75/0.92                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.75/0.92    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 0.75/0.92  thf('0', plain,
% 0.75/0.92      (~ (r1_tarski @ 
% 0.75/0.92          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.92           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.75/0.92           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.75/0.92          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.92           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 0.75/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.92  thf('1', plain,
% 0.75/0.92      ((m1_subset_1 @ sk_B @ 
% 0.75/0.92        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.92  thf(redefinition_k5_setfam_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.93       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X19 : $i, X20 : $i]:
% 0.75/0.93         (((k5_setfam_1 @ X20 @ X19) = (k3_tarski @ X19))
% 0.75/0.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X19 : $i, X20 : $i]:
% 0.75/0.93         (((k5_setfam_1 @ X20 @ X19) = (k3_tarski @ X19))
% 0.75/0.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 0.75/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (~ (r1_tarski @ 
% 0.75/0.93          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 0.75/0.93           (k3_tarski @ sk_C)) @ 
% 0.75/0.93          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['0', '3', '6'])).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(redefinition_k7_subset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.93       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.75/0.93  thf('9', plain,
% 0.75/0.93      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.75/0.93          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.75/0.93           = (k4_xboole_0 @ sk_B @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      (~ (r1_tarski @ 
% 0.75/0.93          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 0.75/0.93           (k3_tarski @ sk_C)) @ 
% 0.75/0.93          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['7', '10'])).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(t3_subset, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (![X21 : $i, X22 : $i]:
% 0.75/0.93         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.93  thf('14', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.93  thf(t109_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 0.75/0.93      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.75/0.93          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['14', '15'])).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (![X21 : $i, X23 : $i]:
% 0.75/0.93         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.75/0.93          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['16', '17'])).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      (![X19 : $i, X20 : $i]:
% 0.75/0.93         (((k5_setfam_1 @ X20 @ X19) = (k3_tarski @ X19))
% 0.75/0.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 0.75/0.93           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      (~ (r1_tarski @ 
% 0.75/0.93          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 0.75/0.93           (k3_tarski @ sk_C)) @ 
% 0.75/0.93          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['11', '20'])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(dt_k5_setfam_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.93       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i]:
% 0.75/0.93         ((m1_subset_1 @ (k5_setfam_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.75/0.93          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.75/0.93      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.75/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.75/0.93          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.75/0.93  thf('28', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 0.75/0.93           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      (~ (r1_tarski @ 
% 0.75/0.93          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 0.75/0.93          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['21', '28'])).
% 0.75/0.93  thf(t96_zfmisc_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 0.75/0.93       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i]:
% 0.75/0.93         ((k3_tarski @ (k2_xboole_0 @ X12 @ X13))
% 0.75/0.93           = (k2_xboole_0 @ (k3_tarski @ X12) @ (k3_tarski @ X13)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.75/0.93  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('31', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.93  thf(t7_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('32', plain,
% 0.75/0.93      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.75/0.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.93  thf('33', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['31', '32'])).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['30', '33'])).
% 0.75/0.93  thf(t39_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('35', plain,
% 0.75/0.93      (![X5 : $i, X6 : $i]:
% 0.75/0.93         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.75/0.93           = (k2_xboole_0 @ X5 @ X6))),
% 0.75/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.75/0.93  thf('36', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i]:
% 0.75/0.93         ((k3_tarski @ (k2_xboole_0 @ X12 @ X13))
% 0.75/0.93           = (k2_xboole_0 @ (k3_tarski @ X12) @ (k3_tarski @ X13)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.75/0.93  thf(t43_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.75/0.93       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.75/0.93  thf('37', plain,
% 0.75/0.93      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.93         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.75/0.93          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.75/0.93          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 0.75/0.93             (k3_tarski @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.93  thf('39', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.75/0.93          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 0.75/0.93             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['35', '38'])).
% 0.75/0.93  thf('40', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 0.75/0.93          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['34', '39'])).
% 0.75/0.93  thf('41', plain, ($false), inference('demod', [status(thm)], ['29', '40'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
