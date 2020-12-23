%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8sd8agyi0V

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:20 EST 2020

% Result     : Theorem 12.02s
% Output     : Refutation 12.02s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 113 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  583 (1451 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t51_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_pre_topc])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','34'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['12','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8sd8agyi0V
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:07:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 12.02/12.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.02/12.23  % Solved by: fo/fo7.sh
% 12.02/12.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.02/12.23  % done 5378 iterations in 11.783s
% 12.02/12.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.02/12.23  % SZS output start Refutation
% 12.02/12.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.02/12.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.02/12.23  thf(sk_A_type, type, sk_A: $i).
% 12.02/12.23  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.02/12.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.02/12.23  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 12.02/12.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.02/12.23  thf(sk_B_type, type, sk_B: $i).
% 12.02/12.23  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.02/12.23  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 12.02/12.23  thf(sk_C_type, type, sk_C: $i).
% 12.02/12.23  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 12.02/12.23  thf(t51_pre_topc, conjecture,
% 12.02/12.23    (![A:$i]:
% 12.02/12.23     ( ( l1_pre_topc @ A ) =>
% 12.02/12.23       ( ![B:$i]:
% 12.02/12.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.02/12.23           ( ![C:$i]:
% 12.02/12.23             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.02/12.23               ( r1_tarski @
% 12.02/12.23                 ( k2_pre_topc @
% 12.02/12.23                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 12.02/12.23                 ( k9_subset_1 @
% 12.02/12.23                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 12.02/12.23                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 12.02/12.23  thf(zf_stmt_0, negated_conjecture,
% 12.02/12.23    (~( ![A:$i]:
% 12.02/12.23        ( ( l1_pre_topc @ A ) =>
% 12.02/12.23          ( ![B:$i]:
% 12.02/12.23            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.02/12.23              ( ![C:$i]:
% 12.02/12.23                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.02/12.23                  ( r1_tarski @
% 12.02/12.23                    ( k2_pre_topc @
% 12.02/12.23                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 12.02/12.23                    ( k9_subset_1 @
% 12.02/12.23                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 12.02/12.23                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 12.02/12.23    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 12.02/12.23  thf('0', plain,
% 12.02/12.23      (~ (r1_tarski @ 
% 12.02/12.23          (k2_pre_topc @ sk_A @ 
% 12.02/12.23           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 12.02/12.23          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 12.02/12.23           (k2_pre_topc @ sk_A @ sk_C)))),
% 12.02/12.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.02/12.23  thf('1', plain,
% 12.02/12.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.02/12.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.02/12.23  thf(redefinition_k9_subset_1, axiom,
% 12.02/12.23    (![A:$i,B:$i,C:$i]:
% 12.02/12.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 12.02/12.23       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 12.02/12.23  thf('2', plain,
% 12.02/12.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.02/12.23         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 12.02/12.23          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 12.02/12.23      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 12.02/12.23  thf('3', plain,
% 12.02/12.23      (![X0 : $i]:
% 12.02/12.23         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 12.02/12.23           = (k3_xboole_0 @ X0 @ sk_C))),
% 12.02/12.23      inference('sup-', [status(thm)], ['1', '2'])).
% 12.02/12.23  thf('4', plain,
% 12.02/12.23      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 12.02/12.23          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 12.02/12.23           (k2_pre_topc @ sk_A @ sk_C)))),
% 12.02/12.23      inference('demod', [status(thm)], ['0', '3'])).
% 12.02/12.23  thf('5', plain,
% 12.02/12.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.02/12.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.02/12.23  thf(dt_k2_pre_topc, axiom,
% 12.02/12.23    (![A:$i,B:$i]:
% 12.02/12.23     ( ( ( l1_pre_topc @ A ) & 
% 12.02/12.23         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.02/12.23       ( m1_subset_1 @
% 12.02/12.23         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 12.02/12.23  thf('6', plain,
% 12.02/12.23      (![X18 : $i, X19 : $i]:
% 12.02/12.23         (~ (l1_pre_topc @ X18)
% 12.02/12.23          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 12.02/12.23          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 12.02/12.23             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 12.02/12.23      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 12.02/12.23  thf('7', plain,
% 12.02/12.23      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 12.02/12.23         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.02/12.23        | ~ (l1_pre_topc @ sk_A))),
% 12.02/12.23      inference('sup-', [status(thm)], ['5', '6'])).
% 12.02/12.23  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 12.02/12.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.02/12.23  thf('9', plain,
% 12.02/12.23      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 12.02/12.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.02/12.23      inference('demod', [status(thm)], ['7', '8'])).
% 12.02/12.23  thf('10', plain,
% 12.02/12.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.02/12.23         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 12.02/12.23          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 12.02/12.23      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 12.02/12.23  thf('11', plain,
% 12.02/12.23      (![X0 : $i]:
% 12.02/12.23         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 12.02/12.23           (k2_pre_topc @ sk_A @ sk_C))
% 12.02/12.23           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 12.02/12.23      inference('sup-', [status(thm)], ['9', '10'])).
% 12.02/12.23  thf('12', plain,
% 12.02/12.23      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 12.02/12.23          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 12.02/12.23           (k2_pre_topc @ sk_A @ sk_C)))),
% 12.02/12.23      inference('demod', [status(thm)], ['4', '11'])).
% 12.02/12.23  thf('13', plain,
% 12.02/12.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.02/12.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.02/12.23  thf('14', plain,
% 12.02/12.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.02/12.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.02/12.23  thf(dt_k9_subset_1, axiom,
% 12.02/12.23    (![A:$i,B:$i,C:$i]:
% 12.02/12.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 12.02/12.23       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 12.02/12.23  thf('15', plain,
% 12.02/12.23      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.02/12.23         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 12.02/12.23          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 12.02/12.23      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 12.02/12.23  thf('16', plain,
% 12.02/12.23      (![X0 : $i]:
% 12.02/12.23         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 12.02/12.23          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.02/12.23      inference('sup-', [status(thm)], ['14', '15'])).
% 12.02/12.23  thf('17', plain,
% 12.02/12.23      (![X0 : $i]:
% 12.02/12.23         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 12.02/12.23           = (k3_xboole_0 @ X0 @ sk_C))),
% 12.02/12.23      inference('sup-', [status(thm)], ['1', '2'])).
% 12.02/12.23  thf('18', plain,
% 12.02/12.23      (![X0 : $i]:
% 12.02/12.23         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 12.02/12.23          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.02/12.23      inference('demod', [status(thm)], ['16', '17'])).
% 12.02/12.23  thf(t49_pre_topc, axiom,
% 12.02/12.23    (![A:$i]:
% 12.02/12.23     ( ( l1_pre_topc @ A ) =>
% 12.02/12.23       ( ![B:$i]:
% 12.02/12.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.02/12.23           ( ![C:$i]:
% 12.02/12.23             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.02/12.23               ( ( r1_tarski @ B @ C ) =>
% 12.02/12.23                 ( r1_tarski @
% 12.02/12.23                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 12.02/12.23  thf('19', plain,
% 12.02/12.23      (![X20 : $i, X21 : $i, X22 : $i]:
% 12.02/12.23         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 12.02/12.23          | ~ (r1_tarski @ X20 @ X22)
% 12.02/12.23          | (r1_tarski @ (k2_pre_topc @ X21 @ X20) @ (k2_pre_topc @ X21 @ X22))
% 12.02/12.23          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 12.02/12.23          | ~ (l1_pre_topc @ X21))),
% 12.02/12.23      inference('cnf', [status(esa)], [t49_pre_topc])).
% 12.02/12.23  thf('20', plain,
% 12.02/12.23      (![X0 : $i, X1 : $i]:
% 12.02/12.23         (~ (l1_pre_topc @ sk_A)
% 12.02/12.23          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.02/12.23          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 12.02/12.23             (k2_pre_topc @ sk_A @ X1))
% 12.02/12.23          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 12.02/12.23      inference('sup-', [status(thm)], ['18', '19'])).
% 12.02/12.23  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 12.02/12.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.02/12.23  thf('22', plain,
% 12.02/12.23      (![X0 : $i, X1 : $i]:
% 12.02/12.23         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.02/12.23          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 12.02/12.23             (k2_pre_topc @ sk_A @ X1))
% 12.02/12.23          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 12.02/12.23      inference('demod', [status(thm)], ['20', '21'])).
% 12.02/12.23  thf('23', plain,
% 12.02/12.23      (![X0 : $i]:
% 12.02/12.23         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 12.02/12.23          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 12.02/12.23             (k2_pre_topc @ sk_A @ sk_C)))),
% 12.02/12.23      inference('sup-', [status(thm)], ['13', '22'])).
% 12.02/12.23  thf(dt_k2_subset_1, axiom,
% 12.02/12.23    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 12.02/12.23  thf('24', plain,
% 12.02/12.23      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 12.02/12.23      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 12.02/12.23  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 12.02/12.23  thf('25', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 12.02/12.23      inference('cnf', [status(esa)], [d4_subset_1])).
% 12.02/12.23  thf('26', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 12.02/12.23      inference('demod', [status(thm)], ['24', '25'])).
% 12.02/12.23  thf('27', plain,
% 12.02/12.23      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.02/12.23         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 12.02/12.23          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 12.02/12.23      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 12.02/12.23  thf('28', plain,
% 12.02/12.23      (![X0 : $i, X1 : $i]:
% 12.02/12.23         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 12.02/12.23      inference('sup-', [status(thm)], ['26', '27'])).
% 12.02/12.23  thf(t3_subset, axiom,
% 12.02/12.23    (![A:$i,B:$i]:
% 12.02/12.23     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.02/12.23  thf('29', plain,
% 12.02/12.23      (![X15 : $i, X16 : $i]:
% 12.02/12.23         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 12.02/12.23      inference('cnf', [status(esa)], [t3_subset])).
% 12.02/12.23  thf('30', plain,
% 12.02/12.23      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 12.02/12.23      inference('sup-', [status(thm)], ['28', '29'])).
% 12.02/12.23  thf('31', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 12.02/12.23      inference('demod', [status(thm)], ['24', '25'])).
% 12.02/12.23  thf('32', plain,
% 12.02/12.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.02/12.23         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 12.02/12.23          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 12.02/12.23      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 12.02/12.23  thf('33', plain,
% 12.02/12.23      (![X0 : $i, X1 : $i]:
% 12.02/12.23         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 12.02/12.23      inference('sup-', [status(thm)], ['31', '32'])).
% 12.02/12.23  thf('34', plain,
% 12.02/12.23      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 12.02/12.23      inference('demod', [status(thm)], ['30', '33'])).
% 12.02/12.23  thf('35', plain,
% 12.02/12.23      (![X0 : $i]:
% 12.02/12.23         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 12.02/12.23          (k2_pre_topc @ sk_A @ sk_C))),
% 12.02/12.23      inference('demod', [status(thm)], ['23', '34'])).
% 12.02/12.23  thf(t17_xboole_1, axiom,
% 12.02/12.23    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 12.02/12.23  thf('36', plain,
% 12.02/12.23      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 12.02/12.23      inference('cnf', [status(esa)], [t17_xboole_1])).
% 12.02/12.23  thf('37', plain,
% 12.02/12.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.02/12.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.02/12.23  thf('38', plain,
% 12.02/12.23      (![X0 : $i, X1 : $i]:
% 12.02/12.23         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.02/12.23          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 12.02/12.23             (k2_pre_topc @ sk_A @ X1))
% 12.02/12.23          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 12.02/12.24      inference('demod', [status(thm)], ['20', '21'])).
% 12.02/12.24  thf('39', plain,
% 12.02/12.24      (![X0 : $i]:
% 12.02/12.24         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_B)
% 12.02/12.24          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 12.02/12.24             (k2_pre_topc @ sk_A @ sk_B)))),
% 12.02/12.24      inference('sup-', [status(thm)], ['37', '38'])).
% 12.02/12.24  thf('40', plain,
% 12.02/12.24      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 12.02/12.24        (k2_pre_topc @ sk_A @ sk_B))),
% 12.02/12.24      inference('sup-', [status(thm)], ['36', '39'])).
% 12.02/12.24  thf(t19_xboole_1, axiom,
% 12.02/12.24    (![A:$i,B:$i,C:$i]:
% 12.02/12.24     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 12.02/12.24       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 12.02/12.24  thf('41', plain,
% 12.02/12.24      (![X2 : $i, X3 : $i, X4 : $i]:
% 12.02/12.24         (~ (r1_tarski @ X2 @ X3)
% 12.02/12.24          | ~ (r1_tarski @ X2 @ X4)
% 12.02/12.24          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 12.02/12.24      inference('cnf', [status(esa)], [t19_xboole_1])).
% 12.02/12.24  thf('42', plain,
% 12.02/12.24      (![X0 : $i]:
% 12.02/12.24         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 12.02/12.24           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))
% 12.02/12.24          | ~ (r1_tarski @ 
% 12.02/12.24               (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ X0))),
% 12.02/12.24      inference('sup-', [status(thm)], ['40', '41'])).
% 12.02/12.24  thf('43', plain,
% 12.02/12.24      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 12.02/12.24        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 12.02/12.24         (k2_pre_topc @ sk_A @ sk_C)))),
% 12.02/12.24      inference('sup-', [status(thm)], ['35', '42'])).
% 12.02/12.24  thf('44', plain, ($false), inference('demod', [status(thm)], ['12', '43'])).
% 12.02/12.24  
% 12.02/12.24  % SZS output end Refutation
% 12.02/12.24  
% 12.02/12.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
