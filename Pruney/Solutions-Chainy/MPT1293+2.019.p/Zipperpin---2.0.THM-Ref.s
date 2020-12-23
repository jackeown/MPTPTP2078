%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6sYLB2Nwn

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:08 EST 2020

% Result     : Theorem 8.45s
% Output     : Refutation 8.45s
% Verified   : 
% Statistics : Number of formulae       :   72 (  89 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  568 (1037 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3','6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ ( k3_tarski @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('15',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('17',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k5_setfam_1 @ X22 @ X21 )
        = ( k3_tarski @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_C ) ) @ ( k3_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','31'])).

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
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ ( k3_tarski @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X15 ) @ ( k3_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X1 ) ) @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['32','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6sYLB2Nwn
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:33:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 8.45/8.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.45/8.66  % Solved by: fo/fo7.sh
% 8.45/8.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.45/8.66  % done 3758 iterations in 8.206s
% 8.45/8.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.45/8.66  % SZS output start Refutation
% 8.45/8.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.45/8.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.45/8.66  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.45/8.66  thf(sk_B_type, type, sk_B: $i).
% 8.45/8.66  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 8.45/8.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.45/8.66  thf(sk_C_type, type, sk_C: $i).
% 8.45/8.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 8.45/8.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.45/8.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.45/8.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 8.45/8.66  thf(sk_A_type, type, sk_A: $i).
% 8.45/8.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.45/8.66  thf(t6_tops_2, conjecture,
% 8.45/8.66    (![A:$i]:
% 8.45/8.66     ( ( l1_struct_0 @ A ) =>
% 8.45/8.66       ( ![B:$i]:
% 8.45/8.66         ( ( m1_subset_1 @
% 8.45/8.66             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.45/8.66           ( ![C:$i]:
% 8.45/8.66             ( ( m1_subset_1 @
% 8.45/8.66                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.45/8.66               ( r1_tarski @
% 8.45/8.66                 ( k7_subset_1 @
% 8.45/8.66                   ( u1_struct_0 @ A ) @ 
% 8.45/8.66                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 8.45/8.66                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 8.45/8.66                 ( k5_setfam_1 @
% 8.45/8.66                   ( u1_struct_0 @ A ) @ 
% 8.45/8.66                   ( k7_subset_1 @
% 8.45/8.66                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ))).
% 8.45/8.66  thf(zf_stmt_0, negated_conjecture,
% 8.45/8.66    (~( ![A:$i]:
% 8.45/8.66        ( ( l1_struct_0 @ A ) =>
% 8.45/8.66          ( ![B:$i]:
% 8.45/8.66            ( ( m1_subset_1 @
% 8.45/8.66                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.45/8.66              ( ![C:$i]:
% 8.45/8.66                ( ( m1_subset_1 @
% 8.45/8.66                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.45/8.66                  ( r1_tarski @
% 8.45/8.66                    ( k7_subset_1 @
% 8.45/8.66                      ( u1_struct_0 @ A ) @ 
% 8.45/8.66                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 8.45/8.66                      ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 8.45/8.66                    ( k5_setfam_1 @
% 8.45/8.66                      ( u1_struct_0 @ A ) @ 
% 8.45/8.66                      ( k7_subset_1 @
% 8.45/8.66                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) ) ) ) ) ) ) ) )),
% 8.45/8.66    inference('cnf.neg', [status(esa)], [t6_tops_2])).
% 8.45/8.66  thf('0', plain,
% 8.45/8.66      (~ (r1_tarski @ 
% 8.45/8.66          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.45/8.66           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 8.45/8.66           (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 8.45/8.66          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 8.45/8.66           (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)))),
% 8.45/8.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.66  thf('1', plain,
% 8.45/8.66      ((m1_subset_1 @ sk_B @ 
% 8.45/8.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.45/8.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.66  thf(redefinition_k5_setfam_1, axiom,
% 8.45/8.66    (![A:$i,B:$i]:
% 8.45/8.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.45/8.66       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 8.45/8.66  thf('2', plain,
% 8.45/8.66      (![X21 : $i, X22 : $i]:
% 8.45/8.66         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 8.45/8.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 8.45/8.66      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 8.45/8.66  thf('3', plain,
% 8.45/8.66      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k3_tarski @ sk_B))),
% 8.45/8.66      inference('sup-', [status(thm)], ['1', '2'])).
% 8.45/8.66  thf('4', plain,
% 8.45/8.66      ((m1_subset_1 @ sk_C @ 
% 8.45/8.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.45/8.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.66  thf('5', plain,
% 8.45/8.66      (![X21 : $i, X22 : $i]:
% 8.45/8.66         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 8.45/8.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 8.45/8.66      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 8.45/8.66  thf('6', plain,
% 8.45/8.66      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 8.45/8.66      inference('sup-', [status(thm)], ['4', '5'])).
% 8.45/8.66  thf('7', plain,
% 8.45/8.66      ((m1_subset_1 @ sk_B @ 
% 8.45/8.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.45/8.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.66  thf(redefinition_k7_subset_1, axiom,
% 8.45/8.66    (![A:$i,B:$i,C:$i]:
% 8.45/8.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.45/8.66       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.45/8.66  thf('8', plain,
% 8.45/8.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.45/8.66         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 8.45/8.66          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 8.45/8.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.45/8.66  thf('9', plain,
% 8.45/8.66      (![X0 : $i]:
% 8.45/8.66         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 8.45/8.66           = (k4_xboole_0 @ sk_B @ X0))),
% 8.45/8.66      inference('sup-', [status(thm)], ['7', '8'])).
% 8.45/8.66  thf('10', plain,
% 8.45/8.66      (~ (r1_tarski @ 
% 8.45/8.66          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ 
% 8.45/8.66           (k3_tarski @ sk_C)) @ 
% 8.45/8.66          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 8.45/8.66      inference('demod', [status(thm)], ['0', '3', '6', '9'])).
% 8.45/8.66  thf('11', plain,
% 8.45/8.66      ((m1_subset_1 @ sk_B @ 
% 8.45/8.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.45/8.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.66  thf(t3_subset, axiom,
% 8.45/8.66    (![A:$i,B:$i]:
% 8.45/8.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.45/8.66  thf('12', plain,
% 8.45/8.66      (![X23 : $i, X24 : $i]:
% 8.45/8.66         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 8.45/8.66      inference('cnf', [status(esa)], [t3_subset])).
% 8.45/8.66  thf('13', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.45/8.66      inference('sup-', [status(thm)], ['11', '12'])).
% 8.45/8.66  thf(t95_zfmisc_1, axiom,
% 8.45/8.66    (![A:$i,B:$i]:
% 8.45/8.66     ( ( r1_tarski @ A @ B ) =>
% 8.45/8.66       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 8.45/8.66  thf('14', plain,
% 8.45/8.66      (![X13 : $i, X14 : $i]:
% 8.45/8.66         ((r1_tarski @ (k3_tarski @ X13) @ (k3_tarski @ X14))
% 8.45/8.66          | ~ (r1_tarski @ X13 @ X14))),
% 8.45/8.66      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 8.45/8.66  thf('15', plain,
% 8.45/8.66      ((r1_tarski @ (k3_tarski @ sk_B) @ 
% 8.45/8.66        (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.45/8.66      inference('sup-', [status(thm)], ['13', '14'])).
% 8.45/8.66  thf(t99_zfmisc_1, axiom,
% 8.45/8.66    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 8.45/8.66  thf('16', plain, (![X17 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X17)) = (X17))),
% 8.45/8.66      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 8.45/8.66  thf('17', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ (u1_struct_0 @ sk_A))),
% 8.45/8.66      inference('demod', [status(thm)], ['15', '16'])).
% 8.45/8.66  thf('18', plain,
% 8.45/8.66      (![X23 : $i, X25 : $i]:
% 8.45/8.66         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 8.45/8.66      inference('cnf', [status(esa)], [t3_subset])).
% 8.45/8.66  thf('19', plain,
% 8.45/8.66      ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.45/8.66      inference('sup-', [status(thm)], ['17', '18'])).
% 8.45/8.66  thf('20', plain,
% 8.45/8.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.45/8.66         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 8.45/8.66          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 8.45/8.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.45/8.66  thf('21', plain,
% 8.45/8.66      (![X0 : $i]:
% 8.45/8.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B) @ X0)
% 8.45/8.66           = (k4_xboole_0 @ (k3_tarski @ sk_B) @ X0))),
% 8.45/8.66      inference('sup-', [status(thm)], ['19', '20'])).
% 8.45/8.66  thf('22', plain,
% 8.45/8.66      (~ (r1_tarski @ 
% 8.45/8.66          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 8.45/8.66          (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 8.45/8.66      inference('demod', [status(thm)], ['10', '21'])).
% 8.45/8.66  thf(t36_xboole_1, axiom,
% 8.45/8.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.45/8.66  thf('23', plain,
% 8.45/8.66      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 8.45/8.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.45/8.66  thf('24', plain,
% 8.45/8.66      ((m1_subset_1 @ sk_B @ 
% 8.45/8.66        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.45/8.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.66  thf(t3_tops_2, axiom,
% 8.45/8.66    (![A:$i]:
% 8.45/8.66     ( ( l1_struct_0 @ A ) =>
% 8.45/8.66       ( ![B:$i]:
% 8.45/8.66         ( ( m1_subset_1 @
% 8.45/8.66             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.45/8.66           ( ![C:$i]:
% 8.45/8.66             ( ( r1_tarski @ C @ B ) =>
% 8.45/8.66               ( m1_subset_1 @
% 8.45/8.66                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 8.45/8.66  thf('25', plain,
% 8.45/8.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.45/8.66         (~ (m1_subset_1 @ X26 @ 
% 8.45/8.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 8.45/8.66          | (m1_subset_1 @ X28 @ 
% 8.45/8.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 8.45/8.66          | ~ (r1_tarski @ X28 @ X26)
% 8.45/8.66          | ~ (l1_struct_0 @ X27))),
% 8.45/8.66      inference('cnf', [status(esa)], [t3_tops_2])).
% 8.45/8.66  thf('26', plain,
% 8.45/8.66      (![X0 : $i]:
% 8.45/8.66         (~ (l1_struct_0 @ sk_A)
% 8.45/8.66          | ~ (r1_tarski @ X0 @ sk_B)
% 8.45/8.66          | (m1_subset_1 @ X0 @ 
% 8.45/8.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.45/8.66      inference('sup-', [status(thm)], ['24', '25'])).
% 8.45/8.66  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 8.45/8.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.45/8.66  thf('28', plain,
% 8.45/8.66      (![X0 : $i]:
% 8.45/8.66         (~ (r1_tarski @ X0 @ sk_B)
% 8.45/8.66          | (m1_subset_1 @ X0 @ 
% 8.45/8.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.45/8.66      inference('demod', [status(thm)], ['26', '27'])).
% 8.45/8.66  thf('29', plain,
% 8.45/8.66      (![X0 : $i]:
% 8.45/8.66         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 8.45/8.66          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.45/8.66      inference('sup-', [status(thm)], ['23', '28'])).
% 8.45/8.66  thf('30', plain,
% 8.45/8.66      (![X21 : $i, X22 : $i]:
% 8.45/8.66         (((k5_setfam_1 @ X22 @ X21) = (k3_tarski @ X21))
% 8.45/8.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 8.45/8.66      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 8.45/8.66  thf('31', plain,
% 8.45/8.66      (![X0 : $i]:
% 8.45/8.66         ((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 8.45/8.66           = (k3_tarski @ (k4_xboole_0 @ sk_B @ X0)))),
% 8.45/8.66      inference('sup-', [status(thm)], ['29', '30'])).
% 8.45/8.66  thf('32', plain,
% 8.45/8.66      (~ (r1_tarski @ 
% 8.45/8.66          (k4_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_C)) @ 
% 8.45/8.66          (k3_tarski @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 8.45/8.66      inference('demod', [status(thm)], ['22', '31'])).
% 8.45/8.66  thf(commutativity_k2_xboole_0, axiom,
% 8.45/8.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 8.45/8.66  thf('33', plain,
% 8.45/8.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.45/8.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.45/8.66  thf(t7_xboole_1, axiom,
% 8.45/8.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 8.45/8.66  thf('34', plain,
% 8.45/8.66      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 8.45/8.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.45/8.66  thf('35', plain,
% 8.45/8.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 8.45/8.66      inference('sup+', [status(thm)], ['33', '34'])).
% 8.45/8.66  thf('36', plain,
% 8.45/8.66      (![X13 : $i, X14 : $i]:
% 8.45/8.66         ((r1_tarski @ (k3_tarski @ X13) @ (k3_tarski @ X14))
% 8.45/8.66          | ~ (r1_tarski @ X13 @ X14))),
% 8.45/8.66      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 8.45/8.66  thf('37', plain,
% 8.45/8.66      (![X0 : $i, X1 : $i]:
% 8.45/8.66         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 8.45/8.66      inference('sup-', [status(thm)], ['35', '36'])).
% 8.45/8.66  thf(t39_xboole_1, axiom,
% 8.45/8.66    (![A:$i,B:$i]:
% 8.45/8.66     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.45/8.66  thf('38', plain,
% 8.45/8.66      (![X4 : $i, X5 : $i]:
% 8.45/8.66         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 8.45/8.66           = (k2_xboole_0 @ X4 @ X5))),
% 8.45/8.66      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.45/8.66  thf(t96_zfmisc_1, axiom,
% 8.45/8.66    (![A:$i,B:$i]:
% 8.45/8.66     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 8.45/8.66       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 8.45/8.66  thf('39', plain,
% 8.45/8.66      (![X15 : $i, X16 : $i]:
% 8.45/8.66         ((k3_tarski @ (k2_xboole_0 @ X15 @ X16))
% 8.45/8.66           = (k2_xboole_0 @ (k3_tarski @ X15) @ (k3_tarski @ X16)))),
% 8.45/8.66      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 8.45/8.66  thf(t43_xboole_1, axiom,
% 8.45/8.66    (![A:$i,B:$i,C:$i]:
% 8.45/8.66     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 8.45/8.66       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 8.45/8.66  thf('40', plain,
% 8.45/8.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.45/8.66         ((r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 8.45/8.66          | ~ (r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 8.45/8.66      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.45/8.66  thf('41', plain,
% 8.45/8.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.45/8.66         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 8.45/8.66          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 8.45/8.66             (k3_tarski @ X0)))),
% 8.45/8.66      inference('sup-', [status(thm)], ['39', '40'])).
% 8.45/8.66  thf('42', plain,
% 8.45/8.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.45/8.66         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 8.45/8.66          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_tarski @ X1)) @ 
% 8.45/8.66             (k3_tarski @ (k4_xboole_0 @ X0 @ X1))))),
% 8.45/8.66      inference('sup-', [status(thm)], ['38', '41'])).
% 8.45/8.66  thf('43', plain,
% 8.45/8.66      (![X0 : $i, X1 : $i]:
% 8.45/8.66         (r1_tarski @ (k4_xboole_0 @ (k3_tarski @ X0) @ (k3_tarski @ X1)) @ 
% 8.45/8.66          (k3_tarski @ (k4_xboole_0 @ X0 @ X1)))),
% 8.45/8.66      inference('sup-', [status(thm)], ['37', '42'])).
% 8.45/8.66  thf('44', plain, ($false), inference('demod', [status(thm)], ['32', '43'])).
% 8.45/8.66  
% 8.45/8.66  % SZS output end Refutation
% 8.45/8.66  
% 8.45/8.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
