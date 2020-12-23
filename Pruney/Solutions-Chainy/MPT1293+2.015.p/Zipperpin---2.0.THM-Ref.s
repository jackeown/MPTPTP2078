%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0jVlxhOfn9

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:08 EST 2020

% Result     : Theorem 3.33s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   66 (  86 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  537 (1036 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k5_setfam_1 @ X25 @ X24 )
        = ( k3_tarski @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','18','27'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X17 ) @ ( k3_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X17 ) @ ( k3_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['28','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0jVlxhOfn9
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.33/3.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.33/3.51  % Solved by: fo/fo7.sh
% 3.33/3.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.33/3.51  % done 3357 iterations in 3.070s
% 3.33/3.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.33/3.51  % SZS output start Refutation
% 3.33/3.51  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.33/3.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.33/3.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.33/3.51  thf(sk_B_type, type, sk_B: $i).
% 3.33/3.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.33/3.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.33/3.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.33/3.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.33/3.51  thf(sk_C_type, type, sk_C: $i).
% 3.33/3.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.33/3.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.33/3.51  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 3.33/3.51  thf(sk_A_type, type, sk_A: $i).
% 3.33/3.51  thf(t6_tops_2, conjecture,
% 3.33/3.51    (![A:$i]:
% 3.33/3.51     ( ( l1_struct_0 @ A ) =>
% 3.33/3.51       ( ![B:$i]:
% 3.33/3.51         ( ( m1_subset_1 @
% 3.33/3.51             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.33/3.51           ( ![C:$i]:
% 3.33/3.51             ( ( m1_subset_1 @
% 3.33/3.51                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.33/3.51               ( r1_tarski @
% 3.33/3.51                 ( k7_subset_1 @
% 3.33/3.51                   ( u1_struct_0 @ A ) @ 
% 3.33/3.51                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 3.33/3.51                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 3.33/3.51                 ( k5_setfam_1 @
% 3.33/3.51                   ( u1_struct_0 @ A ) @ 
% 3.33/3.51                   ( k7_subset_1 @
% 3.33/3.51                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 3.33/3.51  thf(zf_stmt_0, negated_conjecture,
% 3.33/3.51    (~( ![A:$i]:
% 3.33/3.51        ( ( l1_struct_0 @ A ) =>
% 3.33/3.51          ( ![B:$i]:
% 3.33/3.51            ( ( m1_subset_1 @
% 3.33/3.51                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.33/3.51              ( ![C:$i]:
% 3.33/3.51                ( ( m1_subset_1 @
% 3.33/3.51                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.33/3.51                  ( r1_tarski @
% 3.33/3.51                    ( k7_subset_1 @
% 3.33/3.51                      ( u1_struct_0 @ A ) @ 
% 3.33/3.51                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 3.33/3.51                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 3.33/3.51                    ( k5_setfam_1 @
% 3.33/3.51                      ( u1_struct_0 @ A ) @ 
% 3.33/3.51                      ( k7_subset_1 @
% 3.33/3.51                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 3.33/3.51    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 3.33/3.51  thf('0', plain,
% 3.33/3.51      (~ (r1_tarski @ 
% 3.33/3.51          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.33/3.51           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.33/3.51           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 3.33/3.51          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 3.33/3.51           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 3.33/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.51  thf('1', plain,
% 3.33/3.51      ((m1_subset_1 @ sk_B @ 
% 3.33/3.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.51  thf(redefinition_k5_setfam_1, axiom,
% 3.33/3.51    (![A:$i,B:$i]:
% 3.33/3.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.33/3.51       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 3.33/3.51  thf('2', plain,
% 3.33/3.51      (![X24 : $i, X25 : $i]:
% 3.33/3.51         (((k5_setfam_1 @ X25 @ X24) = (k3_tarski @ X24))
% 3.33/3.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 3.33/3.51      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 3.33/3.51  thf('3', plain,
% 3.33/3.51      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 3.33/3.51      inference('sup-', [status(thm)], ['1', '2'])).
% 3.33/3.51  thf('4', plain,
% 3.33/3.51      ((m1_subset_1 @ sk_C @ 
% 3.33/3.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.51  thf('5', plain,
% 3.33/3.51      (![X24 : $i, X25 : $i]:
% 3.33/3.51         (((k5_setfam_1 @ X25 @ X24) = (k3_tarski @ X24))
% 3.33/3.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 3.33/3.51      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 3.33/3.51  thf('6', plain,
% 3.33/3.51      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 3.33/3.51      inference('sup-', [status(thm)], ['4', '5'])).
% 3.33/3.51  thf('7', plain,
% 3.33/3.51      (~ (r1_tarski @ 
% 3.33/3.51          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 3.33/3.51           (k3_tarski @ sk_C)) @ 
% 3.33/3.51          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 3.33/3.51           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 3.33/3.51      inference('demod', [status(thm)], ['0', '3', '6'])).
% 3.33/3.51  thf('8', plain,
% 3.33/3.51      ((m1_subset_1 @ sk_B @ 
% 3.33/3.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.51  thf(redefinition_k7_subset_1, axiom,
% 3.33/3.51    (![A:$i,B:$i,C:$i]:
% 3.33/3.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.33/3.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.33/3.51  thf('9', plain,
% 3.33/3.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.33/3.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 3.33/3.51          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 3.33/3.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.33/3.51  thf('10', plain,
% 3.33/3.51      (![X0 : $i]:
% 3.33/3.51         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 3.33/3.51           = (k4_xboole_0 @ sk_B @ X0))),
% 3.33/3.51      inference('sup-', [status(thm)], ['8', '9'])).
% 3.33/3.51  thf('11', plain,
% 3.33/3.51      (~ (r1_tarski @ 
% 3.33/3.51          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 3.33/3.51           (k3_tarski @ sk_C)) @ 
% 3.33/3.51          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 3.33/3.51      inference('demod', [status(thm)], ['7', '10'])).
% 3.33/3.51  thf('12', plain,
% 3.33/3.51      ((m1_subset_1 @ sk_B @ 
% 3.33/3.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.51  thf(dt_k5_setfam_1, axiom,
% 3.33/3.51    (![A:$i,B:$i]:
% 3.33/3.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.33/3.51       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.33/3.51  thf('13', plain,
% 3.33/3.51      (![X22 : $i, X23 : $i]:
% 3.33/3.51         ((m1_subset_1 @ (k5_setfam_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 3.33/3.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 3.33/3.51      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 3.33/3.51  thf('14', plain,
% 3.33/3.51      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.33/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.51      inference('sup-', [status(thm)], ['12', '13'])).
% 3.33/3.51  thf('15', plain,
% 3.33/3.51      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 3.33/3.51      inference('sup-', [status(thm)], ['1', '2'])).
% 3.33/3.51  thf('16', plain,
% 3.33/3.51      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.51      inference('demod', [status(thm)], ['14', '15'])).
% 3.33/3.51  thf('17', plain,
% 3.33/3.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.33/3.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 3.33/3.51          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 3.33/3.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.33/3.51  thf('18', plain,
% 3.33/3.51      (![X0 : $i]:
% 3.33/3.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 3.33/3.51           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 3.33/3.51      inference('sup-', [status(thm)], ['16', '17'])).
% 3.33/3.51  thf('19', plain,
% 3.33/3.51      ((m1_subset_1 @ sk_B @ 
% 3.33/3.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.51  thf(t3_subset, axiom,
% 3.33/3.51    (![A:$i,B:$i]:
% 3.33/3.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.33/3.51  thf('20', plain,
% 3.33/3.51      (![X26 : $i, X27 : $i]:
% 3.33/3.51         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 3.33/3.51      inference('cnf', [status(esa)], [t3_subset])).
% 3.33/3.51  thf('21', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.51      inference('sup-', [status(thm)], ['19', '20'])).
% 3.33/3.51  thf(t109_xboole_1, axiom,
% 3.33/3.51    (![A:$i,B:$i,C:$i]:
% 3.33/3.51     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 3.33/3.51  thf('22', plain,
% 3.33/3.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.33/3.51         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 3.33/3.51      inference('cnf', [status(esa)], [t109_xboole_1])).
% 3.33/3.51  thf('23', plain,
% 3.33/3.51      (![X0 : $i]:
% 3.33/3.51         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.33/3.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.51      inference('sup-', [status(thm)], ['21', '22'])).
% 3.33/3.51  thf('24', plain,
% 3.33/3.51      (![X26 : $i, X28 : $i]:
% 3.33/3.51         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 3.33/3.51      inference('cnf', [status(esa)], [t3_subset])).
% 3.33/3.51  thf('25', plain,
% 3.33/3.51      (![X0 : $i]:
% 3.33/3.51         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.33/3.51          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.51      inference('sup-', [status(thm)], ['23', '24'])).
% 3.33/3.51  thf('26', plain,
% 3.33/3.51      (![X24 : $i, X25 : $i]:
% 3.33/3.51         (((k5_setfam_1 @ X25 @ X24) = (k3_tarski @ X24))
% 3.33/3.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 3.33/3.51      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 3.33/3.51  thf('27', plain,
% 3.33/3.51      (![X0 : $i]:
% 3.33/3.51         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 3.33/3.51           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 3.33/3.51      inference('sup-', [status(thm)], ['25', '26'])).
% 3.33/3.51  thf('28', plain,
% 3.33/3.51      (~ (r1_tarski @ 
% 3.33/3.51          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 3.33/3.51          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 3.33/3.51      inference('demod', [status(thm)], ['11', '18', '27'])).
% 3.33/3.51  thf(t96_zfmisc_1, axiom,
% 3.33/3.51    (![A:$i,B:$i]:
% 3.33/3.51     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 3.33/3.51       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 3.33/3.51  thf('29', plain,
% 3.33/3.51      (![X17 : $i, X18 : $i]:
% 3.33/3.51         ((k3_tarski @ (k2_xboole_0 @ X17 @ X18))
% 3.33/3.51           = (k2_xboole_0 @ (k3_tarski @ X17) @ (k3_tarski @ X18)))),
% 3.33/3.51      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 3.33/3.51  thf(t36_xboole_1, axiom,
% 3.33/3.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.33/3.51  thf('30', plain,
% 3.33/3.51      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 3.33/3.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.33/3.51  thf(t44_xboole_1, axiom,
% 3.33/3.51    (![A:$i,B:$i,C:$i]:
% 3.33/3.51     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.33/3.51       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.33/3.51  thf('31', plain,
% 3.33/3.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.33/3.51         ((r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 3.33/3.51          | ~ (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14))),
% 3.33/3.51      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.33/3.51  thf('32', plain,
% 3.33/3.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.33/3.51      inference('sup-', [status(thm)], ['30', '31'])).
% 3.33/3.51  thf('33', plain,
% 3.33/3.51      (![X0 : $i, X1 : $i]:
% 3.33/3.51         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 3.33/3.51      inference('sup+', [status(thm)], ['29', '32'])).
% 3.33/3.51  thf(t39_xboole_1, axiom,
% 3.33/3.51    (![A:$i,B:$i]:
% 3.33/3.51     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.33/3.51  thf('34', plain,
% 3.33/3.51      (![X7 : $i, X8 : $i]:
% 3.33/3.51         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 3.33/3.51           = (k2_xboole_0 @ X7 @ X8))),
% 3.33/3.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.33/3.51  thf('35', plain,
% 3.33/3.51      (![X17 : $i, X18 : $i]:
% 3.33/3.51         ((k3_tarski @ (k2_xboole_0 @ X17 @ X18))
% 3.33/3.51           = (k2_xboole_0 @ (k3_tarski @ X17) @ (k3_tarski @ X18)))),
% 3.33/3.51      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 3.33/3.51  thf(t43_xboole_1, axiom,
% 3.33/3.51    (![A:$i,B:$i,C:$i]:
% 3.33/3.51     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.33/3.51       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.33/3.51  thf('36', plain,
% 3.33/3.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.33/3.51         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.33/3.51          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.33/3.51      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.33/3.51  thf('37', plain,
% 3.33/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.51         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 3.33/3.51          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 3.33/3.51             (k3_tarski @ X0)))),
% 3.33/3.51      inference('sup-', [status(thm)], ['35', '36'])).
% 3.33/3.51  thf('38', plain,
% 3.33/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.51         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 3.33/3.51          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 3.33/3.51             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 3.33/3.51      inference('sup-', [status(thm)], ['34', '37'])).
% 3.33/3.51  thf('39', plain,
% 3.33/3.51      (![X0 : $i, X1 : $i]:
% 3.33/3.51         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 3.33/3.51          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 3.33/3.51      inference('sup-', [status(thm)], ['33', '38'])).
% 3.33/3.51  thf('40', plain, ($false), inference('demod', [status(thm)], ['28', '39'])).
% 3.33/3.51  
% 3.33/3.51  % SZS output end Refutation
% 3.33/3.51  
% 3.33/3.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
