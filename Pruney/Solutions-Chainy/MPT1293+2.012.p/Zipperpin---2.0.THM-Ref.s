%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ihHXO0CV15

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:07 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   64 (  88 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  543 (1135 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ( ( k5_setfam_1 @ X25 @ X24 )
        = ( k3_tarski @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k5_setfam_1 @ X25 @ X24 )
        = ( k3_tarski @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X17 @ X16 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( ( k5_setfam_1 @ X25 @ X24 )
        = ( k3_tarski @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ihHXO0CV15
% 0.14/0.36  % Computer   : n017.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:48:31 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.44/1.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.44/1.66  % Solved by: fo/fo7.sh
% 1.44/1.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.66  % done 1171 iterations in 1.195s
% 1.44/1.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.44/1.66  % SZS output start Refutation
% 1.44/1.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.44/1.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.44/1.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.44/1.66  thf(sk_B_type, type, sk_B: $i).
% 1.44/1.66  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.66  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.44/1.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.44/1.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.44/1.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.44/1.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.44/1.66  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.44/1.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.44/1.66  thf(sk_C_type, type, sk_C: $i).
% 1.44/1.66  thf(t6_tops_2, conjecture,
% 1.44/1.66    (![A:$i]:
% 1.44/1.66     ( ( l1_struct_0 @ A ) =>
% 1.44/1.66       ( ![B:$i]:
% 1.44/1.66         ( ( m1_subset_1 @
% 1.44/1.66             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.44/1.66           ( ![C:$i]:
% 1.44/1.66             ( ( m1_subset_1 @
% 1.44/1.66                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.44/1.66               ( r1_tarski @
% 1.44/1.66                 ( k7_subset_1 @
% 1.44/1.66                   ( u1_struct_0 @ A ) @ 
% 1.44/1.66                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.44/1.66                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 1.44/1.66                 ( k5_setfam_1 @
% 1.44/1.66                   ( u1_struct_0 @ A ) @ 
% 1.44/1.66                   ( k7_subset_1 @
% 1.44/1.66                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 1.44/1.66  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.66    (~( ![A:$i]:
% 1.44/1.66        ( ( l1_struct_0 @ A ) =>
% 1.44/1.66          ( ![B:$i]:
% 1.44/1.66            ( ( m1_subset_1 @
% 1.44/1.66                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.44/1.66              ( ![C:$i]:
% 1.44/1.66                ( ( m1_subset_1 @
% 1.44/1.66                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.44/1.66                  ( r1_tarski @
% 1.44/1.66                    ( k7_subset_1 @
% 1.44/1.66                      ( u1_struct_0 @ A ) @ 
% 1.44/1.66                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.44/1.66                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 1.44/1.66                    ( k5_setfam_1 @
% 1.44/1.66                      ( u1_struct_0 @ A ) @ 
% 1.44/1.66                      ( k7_subset_1 @
% 1.44/1.66                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 1.44/1.66    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 1.44/1.66  thf('0', plain,
% 1.44/1.66      (~ (r1_tarski @ 
% 1.44/1.66          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.66           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.44/1.66           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.44/1.66          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.66           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('1', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_B @ 
% 1.44/1.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf(redefinition_k5_setfam_1, axiom,
% 1.44/1.66    (![A:$i,B:$i]:
% 1.44/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.44/1.66       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 1.44/1.66  thf('2', plain,
% 1.44/1.66      (![X24 : $i, X25 : $i]:
% 1.44/1.66         (((k5_setfam_1 @ X25 @ X24) = (k3_tarski @ X24))
% 1.44/1.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 1.44/1.66      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.44/1.66  thf('3', plain,
% 1.44/1.66      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 1.44/1.66      inference('sup-', [status(thm)], ['1', '2'])).
% 1.44/1.66  thf('4', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_C @ 
% 1.44/1.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('5', plain,
% 1.44/1.66      (![X24 : $i, X25 : $i]:
% 1.44/1.66         (((k5_setfam_1 @ X25 @ X24) = (k3_tarski @ X24))
% 1.44/1.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 1.44/1.66      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.44/1.66  thf('6', plain,
% 1.44/1.66      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 1.44/1.66      inference('sup-', [status(thm)], ['4', '5'])).
% 1.44/1.66  thf('7', plain,
% 1.44/1.66      (~ (r1_tarski @ 
% 1.44/1.66          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.44/1.66           (k3_tarski @ sk_C)) @ 
% 1.44/1.66          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.44/1.66           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 1.44/1.66      inference('demod', [status(thm)], ['0', '3', '6'])).
% 1.44/1.66  thf('8', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_B @ 
% 1.44/1.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf(redefinition_k7_subset_1, axiom,
% 1.44/1.66    (![A:$i,B:$i,C:$i]:
% 1.44/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.66       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.44/1.66  thf('9', plain,
% 1.44/1.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.44/1.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.44/1.66          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 1.44/1.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.44/1.66  thf('10', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 1.44/1.66           = (k4_xboole_0 @ sk_B @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['8', '9'])).
% 1.44/1.66  thf('11', plain,
% 1.44/1.66      (~ (r1_tarski @ 
% 1.44/1.66          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 1.44/1.66           (k3_tarski @ sk_C)) @ 
% 1.44/1.66          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.44/1.66      inference('demod', [status(thm)], ['7', '10'])).
% 1.44/1.66  thf('12', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_B @ 
% 1.44/1.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf(dt_k5_setfam_1, axiom,
% 1.44/1.66    (![A:$i,B:$i]:
% 1.44/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.44/1.66       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.44/1.66  thf('13', plain,
% 1.44/1.66      (![X22 : $i, X23 : $i]:
% 1.44/1.66         ((m1_subset_1 @ (k5_setfam_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 1.44/1.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 1.44/1.66      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 1.44/1.66  thf('14', plain,
% 1.44/1.66      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.44/1.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['12', '13'])).
% 1.44/1.66  thf('15', plain,
% 1.44/1.66      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 1.44/1.66      inference('sup-', [status(thm)], ['1', '2'])).
% 1.44/1.66  thf('16', plain,
% 1.44/1.66      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.44/1.66      inference('demod', [status(thm)], ['14', '15'])).
% 1.44/1.66  thf('17', plain,
% 1.44/1.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.44/1.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.44/1.66          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 1.44/1.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.44/1.66  thf('18', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 1.44/1.66           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['16', '17'])).
% 1.44/1.66  thf('19', plain,
% 1.44/1.66      (~ (r1_tarski @ 
% 1.44/1.66          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 1.44/1.66          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.44/1.66      inference('demod', [status(thm)], ['11', '18'])).
% 1.44/1.66  thf('20', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_B @ 
% 1.44/1.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf(dt_k7_subset_1, axiom,
% 1.44/1.66    (![A:$i,B:$i,C:$i]:
% 1.44/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.44/1.66       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.44/1.66  thf('21', plain,
% 1.44/1.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.44/1.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.44/1.66          | (m1_subset_1 @ (k7_subset_1 @ X17 @ X16 @ X18) @ 
% 1.44/1.66             (k1_zfmisc_1 @ X17)))),
% 1.44/1.66      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.44/1.66  thf('22', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         (m1_subset_1 @ 
% 1.44/1.66          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 1.44/1.66          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.44/1.66      inference('sup-', [status(thm)], ['20', '21'])).
% 1.44/1.66  thf('23', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 1.44/1.66           = (k4_xboole_0 @ sk_B @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['8', '9'])).
% 1.44/1.66  thf('24', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.44/1.66          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.44/1.66      inference('demod', [status(thm)], ['22', '23'])).
% 1.44/1.66  thf('25', plain,
% 1.44/1.66      (![X24 : $i, X25 : $i]:
% 1.44/1.66         (((k5_setfam_1 @ X25 @ X24) = (k3_tarski @ X24))
% 1.44/1.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 1.44/1.66      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.44/1.66  thf('26', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 1.44/1.66           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['24', '25'])).
% 1.44/1.66  thf('27', plain,
% 1.44/1.66      (~ (r1_tarski @ 
% 1.44/1.66          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 1.44/1.66          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.44/1.66      inference('demod', [status(thm)], ['19', '26'])).
% 1.44/1.66  thf(t96_zfmisc_1, axiom,
% 1.44/1.66    (![A:$i,B:$i]:
% 1.44/1.66     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 1.44/1.66       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 1.44/1.66  thf('28', plain,
% 1.44/1.66      (![X14 : $i, X15 : $i]:
% 1.44/1.66         ((k3_tarski @ (k2_xboole_0 @ X14 @ X15))
% 1.44/1.66           = (k2_xboole_0 @ (k3_tarski @ X14) @ (k3_tarski @ X15)))),
% 1.44/1.66      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 1.44/1.66  thf(t36_xboole_1, axiom,
% 1.44/1.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.44/1.66  thf('29', plain,
% 1.44/1.66      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 1.44/1.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.44/1.66  thf(t44_xboole_1, axiom,
% 1.44/1.66    (![A:$i,B:$i,C:$i]:
% 1.44/1.66     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.44/1.66       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.44/1.66  thf('30', plain,
% 1.44/1.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.44/1.66         ((r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 1.44/1.66          | ~ (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11))),
% 1.44/1.66      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.44/1.66  thf('31', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['29', '30'])).
% 1.44/1.66  thf('32', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]:
% 1.44/1.66         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 1.44/1.66      inference('sup+', [status(thm)], ['28', '31'])).
% 1.44/1.66  thf(t39_xboole_1, axiom,
% 1.44/1.66    (![A:$i,B:$i]:
% 1.44/1.66     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.44/1.66  thf('33', plain,
% 1.44/1.66      (![X4 : $i, X5 : $i]:
% 1.44/1.66         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 1.44/1.66           = (k2_xboole_0 @ X4 @ X5))),
% 1.44/1.66      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.44/1.66  thf('34', plain,
% 1.44/1.66      (![X14 : $i, X15 : $i]:
% 1.44/1.66         ((k3_tarski @ (k2_xboole_0 @ X14 @ X15))
% 1.44/1.66           = (k2_xboole_0 @ (k3_tarski @ X14) @ (k3_tarski @ X15)))),
% 1.44/1.66      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 1.44/1.66  thf(t43_xboole_1, axiom,
% 1.44/1.66    (![A:$i,B:$i,C:$i]:
% 1.44/1.66     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.44/1.66       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.44/1.66  thf('35', plain,
% 1.44/1.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.44/1.66         ((r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 1.44/1.66          | ~ (r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.44/1.66      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.44/1.66  thf('36', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.66         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 1.44/1.66          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 1.44/1.66             (k3_tarski @ X0)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['34', '35'])).
% 1.44/1.66  thf('37', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.66         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 1.44/1.66          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 1.44/1.66             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 1.44/1.66      inference('sup-', [status(thm)], ['33', '36'])).
% 1.44/1.66  thf('38', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]:
% 1.44/1.66         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 1.44/1.66          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['32', '37'])).
% 1.44/1.66  thf('39', plain, ($false), inference('demod', [status(thm)], ['27', '38'])).
% 1.44/1.66  
% 1.44/1.66  % SZS output end Refutation
% 1.44/1.66  
% 1.44/1.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
