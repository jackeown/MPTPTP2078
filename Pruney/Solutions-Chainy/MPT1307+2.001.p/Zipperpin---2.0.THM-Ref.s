%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hrPoGQapcn

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:26 EST 2020

% Result     : Theorem 3.17s
% Output     : Refutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   74 (  95 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  530 ( 851 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t25_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v2_tops_2 @ B @ A )
               => ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v2_tops_2 @ B @ A )
                 => ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_tops_2])).

thf('0',plain,(
    ~ ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    = ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['6','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t19_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ B @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) )
      | ( v2_tops_2 @ X25 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ~ ( v2_tops_2 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t19_tops_2])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','42'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( v2_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['4','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hrPoGQapcn
% 0.11/0.35  % Computer   : n012.cluster.edu
% 0.11/0.35  % Model      : x86_64 x86_64
% 0.11/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.35  % Memory     : 8042.1875MB
% 0.11/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.35  % CPULimit   : 60
% 0.11/0.35  % DateTime   : Tue Dec  1 16:53:07 EST 2020
% 0.11/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 3.17/3.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.17/3.42  % Solved by: fo/fo7.sh
% 3.17/3.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.17/3.42  % done 5370 iterations in 2.957s
% 3.17/3.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.17/3.42  % SZS output start Refutation
% 3.17/3.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.17/3.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.17/3.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.17/3.42  thf(sk_A_type, type, sk_A: $i).
% 3.17/3.42  thf(sk_C_type, type, sk_C: $i).
% 3.17/3.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.17/3.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.17/3.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.17/3.42  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.17/3.42  thf(sk_B_type, type, sk_B: $i).
% 3.17/3.42  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 3.17/3.42  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.17/3.42  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.17/3.42  thf(t25_tops_2, conjecture,
% 3.17/3.42    (![A:$i]:
% 3.17/3.42     ( ( l1_pre_topc @ A ) =>
% 3.17/3.42       ( ![B:$i]:
% 3.17/3.42         ( ( m1_subset_1 @
% 3.17/3.42             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.17/3.42           ( ![C:$i]:
% 3.17/3.42             ( ( m1_subset_1 @
% 3.17/3.42                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.17/3.42               ( ( v2_tops_2 @ B @ A ) =>
% 3.17/3.42                 ( v2_tops_2 @
% 3.17/3.42                   ( k7_subset_1 @
% 3.17/3.42                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 3.17/3.42                   A ) ) ) ) ) ) ))).
% 3.17/3.42  thf(zf_stmt_0, negated_conjecture,
% 3.17/3.42    (~( ![A:$i]:
% 3.17/3.42        ( ( l1_pre_topc @ A ) =>
% 3.17/3.42          ( ![B:$i]:
% 3.17/3.42            ( ( m1_subset_1 @
% 3.17/3.42                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.17/3.42              ( ![C:$i]:
% 3.17/3.42                ( ( m1_subset_1 @
% 3.17/3.42                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.17/3.42                  ( ( v2_tops_2 @ B @ A ) =>
% 3.17/3.42                    ( v2_tops_2 @
% 3.17/3.42                      ( k7_subset_1 @
% 3.17/3.42                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 3.17/3.42                      A ) ) ) ) ) ) ) )),
% 3.17/3.42    inference('cnf.neg', [status(esa)], [t25_tops_2])).
% 3.17/3.42  thf('0', plain,
% 3.17/3.42      (~ (v2_tops_2 @ 
% 3.17/3.42          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 3.17/3.42          sk_A)),
% 3.17/3.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.42  thf('1', plain,
% 3.17/3.42      ((m1_subset_1 @ sk_B @ 
% 3.17/3.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.17/3.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.42  thf(redefinition_k7_subset_1, axiom,
% 3.17/3.42    (![A:$i,B:$i,C:$i]:
% 3.17/3.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.17/3.42       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.17/3.42  thf('2', plain,
% 3.17/3.42      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.17/3.42         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 3.17/3.42          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 3.17/3.42      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.17/3.42  thf('3', plain,
% 3.17/3.42      (![X0 : $i]:
% 3.17/3.42         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 3.17/3.42           = (k4_xboole_0 @ sk_B @ X0))),
% 3.17/3.42      inference('sup-', [status(thm)], ['1', '2'])).
% 3.17/3.42  thf('4', plain, (~ (v2_tops_2 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 3.17/3.42      inference('demod', [status(thm)], ['0', '3'])).
% 3.17/3.42  thf('5', plain,
% 3.17/3.42      ((m1_subset_1 @ sk_B @ 
% 3.17/3.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.17/3.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.42  thf(commutativity_k2_xboole_0, axiom,
% 3.17/3.42    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.17/3.42  thf('6', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.17/3.42      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.17/3.42  thf('7', plain,
% 3.17/3.42      ((m1_subset_1 @ sk_B @ 
% 3.17/3.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.17/3.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.42  thf(t3_subset, axiom,
% 3.17/3.42    (![A:$i,B:$i]:
% 3.17/3.42     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.17/3.42  thf('8', plain,
% 3.17/3.42      (![X22 : $i, X23 : $i]:
% 3.17/3.42         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 3.17/3.42      inference('cnf', [status(esa)], [t3_subset])).
% 3.17/3.42  thf('9', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.17/3.42      inference('sup-', [status(thm)], ['7', '8'])).
% 3.17/3.42  thf(t12_xboole_1, axiom,
% 3.17/3.42    (![A:$i,B:$i]:
% 3.17/3.42     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.17/3.42  thf('10', plain,
% 3.17/3.42      (![X5 : $i, X6 : $i]:
% 3.17/3.42         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.17/3.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.17/3.42  thf('11', plain,
% 3.17/3.42      (((k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.17/3.42         = (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.17/3.42      inference('sup-', [status(thm)], ['9', '10'])).
% 3.17/3.42  thf(t41_xboole_1, axiom,
% 3.17/3.42    (![A:$i,B:$i,C:$i]:
% 3.17/3.42     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.17/3.42       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.17/3.42  thf('12', plain,
% 3.17/3.42      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.17/3.42         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.17/3.42           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.17/3.42      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.17/3.42  thf(t36_xboole_1, axiom,
% 3.17/3.42    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.17/3.42  thf('13', plain,
% 3.17/3.42      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 3.17/3.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.17/3.42  thf('14', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.17/3.42         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 3.17/3.42          (k4_xboole_0 @ X2 @ X1))),
% 3.17/3.42      inference('sup+', [status(thm)], ['12', '13'])).
% 3.17/3.42  thf('15', plain,
% 3.17/3.42      (![X0 : $i]:
% 3.17/3.42         (r1_tarski @ 
% 3.17/3.42          (k4_xboole_0 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 3.17/3.42          (k4_xboole_0 @ X0 @ sk_B))),
% 3.17/3.42      inference('sup+', [status(thm)], ['11', '14'])).
% 3.17/3.42  thf('16', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.17/3.42      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.17/3.42  thf('17', plain,
% 3.17/3.42      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 3.17/3.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.17/3.42  thf(t44_xboole_1, axiom,
% 3.17/3.42    (![A:$i,B:$i,C:$i]:
% 3.17/3.42     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.17/3.42       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.17/3.42  thf('18', plain,
% 3.17/3.42      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.17/3.42         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 3.17/3.42          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 3.17/3.42      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.17/3.42  thf('19', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.17/3.42      inference('sup-', [status(thm)], ['17', '18'])).
% 3.17/3.42  thf('20', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.17/3.42      inference('sup+', [status(thm)], ['16', '19'])).
% 3.17/3.42  thf(t43_xboole_1, axiom,
% 3.17/3.42    (![A:$i,B:$i,C:$i]:
% 3.17/3.42     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.17/3.42       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.17/3.42  thf('21', plain,
% 3.17/3.42      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.17/3.42         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 3.17/3.42          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 3.17/3.42      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.17/3.42  thf('22', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 3.17/3.42      inference('sup-', [status(thm)], ['20', '21'])).
% 3.17/3.42  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.17/3.42  thf('23', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.17/3.42      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.17/3.42  thf(d10_xboole_0, axiom,
% 3.17/3.42    (![A:$i,B:$i]:
% 3.17/3.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.17/3.42  thf('24', plain,
% 3.17/3.42      (![X2 : $i, X4 : $i]:
% 3.17/3.42         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 3.17/3.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.17/3.42  thf('25', plain,
% 3.17/3.42      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.17/3.42      inference('sup-', [status(thm)], ['23', '24'])).
% 3.17/3.42  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.17/3.42      inference('sup-', [status(thm)], ['22', '25'])).
% 3.17/3.42  thf('27', plain,
% 3.17/3.42      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.17/3.42      inference('sup-', [status(thm)], ['23', '24'])).
% 3.17/3.42  thf('28', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i]:
% 3.17/3.42         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 3.17/3.42      inference('sup-', [status(thm)], ['26', '27'])).
% 3.17/3.42  thf('29', plain,
% 3.17/3.42      (((k4_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.17/3.42         = (k1_xboole_0))),
% 3.17/3.42      inference('sup-', [status(thm)], ['15', '28'])).
% 3.17/3.42  thf('30', plain,
% 3.17/3.42      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.17/3.42         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 3.17/3.42          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 3.17/3.42      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.17/3.42  thf('31', plain,
% 3.17/3.42      (![X0 : $i]:
% 3.17/3.42         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.17/3.42          | (r1_tarski @ sk_B @ 
% 3.17/3.42             (k2_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0)))),
% 3.17/3.42      inference('sup-', [status(thm)], ['29', '30'])).
% 3.17/3.42  thf('32', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.17/3.42      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.17/3.42  thf('33', plain,
% 3.17/3.42      (![X0 : $i]:
% 3.17/3.42         (r1_tarski @ sk_B @ 
% 3.17/3.42          (k2_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 3.17/3.42      inference('demod', [status(thm)], ['31', '32'])).
% 3.17/3.42  thf('34', plain,
% 3.17/3.42      (![X0 : $i]:
% 3.17/3.42         (r1_tarski @ sk_B @ 
% 3.17/3.42          (k2_xboole_0 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.17/3.42      inference('sup+', [status(thm)], ['6', '33'])).
% 3.17/3.42  thf('35', plain,
% 3.17/3.42      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.17/3.42         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 3.17/3.42          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 3.17/3.42      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.17/3.42  thf('36', plain,
% 3.17/3.42      (![X0 : $i]:
% 3.17/3.42         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.17/3.42          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.17/3.42      inference('sup-', [status(thm)], ['34', '35'])).
% 3.17/3.42  thf('37', plain,
% 3.17/3.42      (![X22 : $i, X24 : $i]:
% 3.17/3.42         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 3.17/3.42      inference('cnf', [status(esa)], [t3_subset])).
% 3.17/3.42  thf('38', plain,
% 3.17/3.42      (![X0 : $i]:
% 3.17/3.42         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.17/3.42          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.17/3.42      inference('sup-', [status(thm)], ['36', '37'])).
% 3.17/3.42  thf(t19_tops_2, axiom,
% 3.17/3.42    (![A:$i]:
% 3.17/3.42     ( ( l1_pre_topc @ A ) =>
% 3.17/3.42       ( ![B:$i]:
% 3.17/3.42         ( ( m1_subset_1 @
% 3.17/3.42             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.17/3.42           ( ![C:$i]:
% 3.17/3.42             ( ( m1_subset_1 @
% 3.17/3.42                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.17/3.42               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 3.17/3.42                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 3.17/3.42  thf('39', plain,
% 3.17/3.42      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.17/3.42         (~ (m1_subset_1 @ X25 @ 
% 3.17/3.42             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26))))
% 3.17/3.42          | (v2_tops_2 @ X25 @ X26)
% 3.17/3.42          | ~ (r1_tarski @ X25 @ X27)
% 3.17/3.42          | ~ (v2_tops_2 @ X27 @ X26)
% 3.17/3.42          | ~ (m1_subset_1 @ X27 @ 
% 3.17/3.42               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26))))
% 3.17/3.42          | ~ (l1_pre_topc @ X26))),
% 3.17/3.42      inference('cnf', [status(esa)], [t19_tops_2])).
% 3.17/3.42  thf('40', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i]:
% 3.17/3.42         (~ (l1_pre_topc @ sk_A)
% 3.17/3.42          | ~ (m1_subset_1 @ X1 @ 
% 3.17/3.42               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 3.17/3.42          | ~ (v2_tops_2 @ X1 @ sk_A)
% 3.17/3.42          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 3.17/3.42          | (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 3.17/3.42      inference('sup-', [status(thm)], ['38', '39'])).
% 3.17/3.42  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 3.17/3.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.42  thf('42', plain,
% 3.17/3.42      (![X0 : $i, X1 : $i]:
% 3.17/3.42         (~ (m1_subset_1 @ X1 @ 
% 3.17/3.42             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 3.17/3.42          | ~ (v2_tops_2 @ X1 @ sk_A)
% 3.17/3.42          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 3.17/3.42          | (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 3.17/3.42      inference('demod', [status(thm)], ['40', '41'])).
% 3.17/3.42  thf('43', plain,
% 3.17/3.42      (![X0 : $i]:
% 3.17/3.42         ((v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 3.17/3.42          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 3.17/3.42          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 3.17/3.42      inference('sup-', [status(thm)], ['5', '42'])).
% 3.17/3.42  thf('44', plain,
% 3.17/3.42      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 3.17/3.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.17/3.42  thf('45', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 3.17/3.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.42  thf('46', plain,
% 3.17/3.42      (![X0 : $i]: (v2_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 3.17/3.42      inference('demod', [status(thm)], ['43', '44', '45'])).
% 3.17/3.42  thf('47', plain, ($false), inference('demod', [status(thm)], ['4', '46'])).
% 3.17/3.42  
% 3.17/3.42  % SZS output end Refutation
% 3.17/3.42  
% 3.17/3.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
