%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.etL3Xncotj

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:21 EST 2020

% Result     : Theorem 25.51s
% Output     : Refutation 25.51s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 111 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  526 ( 974 expanded)
%              Number of equality atoms :   14 (  29 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t22_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k4_xboole_0 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r2_hidden @ X54 @ X55 )
      | ( v1_xboole_0 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X46: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X44 @ X43 )
      | ( r1_tarski @ X44 @ X42 )
      | ( X43
       != ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ X44 @ X42 )
      | ~ ( r2_hidden @ X44 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X7 ) ) @ X6 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k5_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ X41 @ X42 )
      | ( r2_hidden @ X41 @ X43 )
      | ( X43
       != ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('32',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X41 @ X42 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X52: $i,X53: $i] :
      ( ( m1_subset_1 @ X52 @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t18_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) ) )
      | ( v1_tops_2 @ X56 @ X57 )
      | ~ ( r1_tarski @ X56 @ X58 )
      | ~ ( v1_tops_2 @ X58 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('42',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['4','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.etL3Xncotj
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:17:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 25.51/25.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 25.51/25.69  % Solved by: fo/fo7.sh
% 25.51/25.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.51/25.69  % done 4781 iterations in 25.228s
% 25.51/25.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 25.51/25.69  % SZS output start Refutation
% 25.51/25.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 25.51/25.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 25.51/25.69  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 25.51/25.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 25.51/25.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 25.51/25.69  thf(sk_B_type, type, sk_B: $i).
% 25.51/25.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 25.51/25.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 25.51/25.69  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 25.51/25.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 25.51/25.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 25.51/25.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 25.51/25.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 25.51/25.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 25.51/25.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 25.51/25.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 25.51/25.69  thf(sk_A_type, type, sk_A: $i).
% 25.51/25.69  thf(t22_tops_2, conjecture,
% 25.51/25.69    (![A:$i]:
% 25.51/25.69     ( ( l1_pre_topc @ A ) =>
% 25.51/25.69       ( ![B:$i]:
% 25.51/25.69         ( ( m1_subset_1 @
% 25.51/25.69             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 25.51/25.69           ( ![C:$i]:
% 25.51/25.69             ( ( m1_subset_1 @
% 25.51/25.69                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 25.51/25.69               ( ( v1_tops_2 @ B @ A ) =>
% 25.51/25.69                 ( v1_tops_2 @
% 25.51/25.69                   ( k7_subset_1 @
% 25.51/25.69                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 25.51/25.69                   A ) ) ) ) ) ) ))).
% 25.51/25.69  thf(zf_stmt_0, negated_conjecture,
% 25.51/25.69    (~( ![A:$i]:
% 25.51/25.69        ( ( l1_pre_topc @ A ) =>
% 25.51/25.69          ( ![B:$i]:
% 25.51/25.69            ( ( m1_subset_1 @
% 25.51/25.69                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 25.51/25.69              ( ![C:$i]:
% 25.51/25.69                ( ( m1_subset_1 @
% 25.51/25.69                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 25.51/25.69                  ( ( v1_tops_2 @ B @ A ) =>
% 25.51/25.69                    ( v1_tops_2 @
% 25.51/25.69                      ( k7_subset_1 @
% 25.51/25.69                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 25.51/25.69                      A ) ) ) ) ) ) ) )),
% 25.51/25.69    inference('cnf.neg', [status(esa)], [t22_tops_2])).
% 25.51/25.69  thf('0', plain,
% 25.51/25.69      (~ (v1_tops_2 @ 
% 25.51/25.69          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 25.51/25.69          sk_A)),
% 25.51/25.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.51/25.69  thf('1', plain,
% 25.51/25.69      ((m1_subset_1 @ sk_B @ 
% 25.51/25.69        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 25.51/25.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.51/25.69  thf(redefinition_k7_subset_1, axiom,
% 25.51/25.69    (![A:$i,B:$i,C:$i]:
% 25.51/25.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 25.51/25.69       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 25.51/25.69  thf('2', plain,
% 25.51/25.69      (![X47 : $i, X48 : $i, X49 : $i]:
% 25.51/25.69         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 25.51/25.69          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k4_xboole_0 @ X47 @ X49)))),
% 25.51/25.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 25.51/25.69  thf('3', plain,
% 25.51/25.69      (![X0 : $i]:
% 25.51/25.69         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 25.51/25.69           = (k4_xboole_0 @ sk_B @ X0))),
% 25.51/25.69      inference('sup-', [status(thm)], ['1', '2'])).
% 25.51/25.69  thf('4', plain, (~ (v1_tops_2 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 25.51/25.69      inference('demod', [status(thm)], ['0', '3'])).
% 25.51/25.69  thf('5', plain,
% 25.51/25.69      ((m1_subset_1 @ sk_B @ 
% 25.51/25.69        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 25.51/25.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.51/25.69  thf('6', plain,
% 25.51/25.69      ((m1_subset_1 @ sk_B @ 
% 25.51/25.69        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 25.51/25.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.51/25.69  thf(t2_subset, axiom,
% 25.51/25.69    (![A:$i,B:$i]:
% 25.51/25.69     ( ( m1_subset_1 @ A @ B ) =>
% 25.51/25.69       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 25.51/25.69  thf('7', plain,
% 25.51/25.69      (![X54 : $i, X55 : $i]:
% 25.51/25.69         ((r2_hidden @ X54 @ X55)
% 25.51/25.69          | (v1_xboole_0 @ X55)
% 25.51/25.69          | ~ (m1_subset_1 @ X54 @ X55))),
% 25.51/25.69      inference('cnf', [status(esa)], [t2_subset])).
% 25.51/25.69  thf('8', plain,
% 25.51/25.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 25.51/25.69        | (r2_hidden @ sk_B @ 
% 25.51/25.69           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 25.51/25.69      inference('sup-', [status(thm)], ['6', '7'])).
% 25.51/25.69  thf(fc1_subset_1, axiom,
% 25.51/25.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 25.51/25.69  thf('9', plain, (![X46 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 25.51/25.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 25.51/25.69  thf('10', plain,
% 25.51/25.69      ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 25.51/25.69      inference('clc', [status(thm)], ['8', '9'])).
% 25.51/25.69  thf(d1_zfmisc_1, axiom,
% 25.51/25.69    (![A:$i,B:$i]:
% 25.51/25.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 25.51/25.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 25.51/25.69  thf('11', plain,
% 25.51/25.69      (![X42 : $i, X43 : $i, X44 : $i]:
% 25.51/25.69         (~ (r2_hidden @ X44 @ X43)
% 25.51/25.69          | (r1_tarski @ X44 @ X42)
% 25.51/25.69          | ((X43) != (k1_zfmisc_1 @ X42)))),
% 25.51/25.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 25.51/25.69  thf('12', plain,
% 25.51/25.69      (![X42 : $i, X44 : $i]:
% 25.51/25.69         ((r1_tarski @ X44 @ X42) | ~ (r2_hidden @ X44 @ (k1_zfmisc_1 @ X42)))),
% 25.51/25.69      inference('simplify', [status(thm)], ['11'])).
% 25.51/25.69  thf('13', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 25.51/25.69      inference('sup-', [status(thm)], ['10', '12'])).
% 25.51/25.69  thf(d10_xboole_0, axiom,
% 25.51/25.69    (![A:$i,B:$i]:
% 25.51/25.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 25.51/25.69  thf('14', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 25.51/25.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.51/25.69  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 25.51/25.69      inference('simplify', [status(thm)], ['14'])).
% 25.51/25.69  thf(t108_xboole_1, axiom,
% 25.51/25.69    (![A:$i,B:$i,C:$i]:
% 25.51/25.69     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 25.51/25.69  thf('16', plain,
% 25.51/25.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 25.51/25.69         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 25.51/25.69      inference('cnf', [status(esa)], [t108_xboole_1])).
% 25.51/25.69  thf(t12_setfam_1, axiom,
% 25.51/25.69    (![A:$i,B:$i]:
% 25.51/25.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 25.51/25.69  thf('17', plain,
% 25.51/25.69      (![X50 : $i, X51 : $i]:
% 25.51/25.69         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 25.51/25.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 25.51/25.69  thf('18', plain,
% 25.51/25.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 25.51/25.69         (~ (r1_tarski @ X5 @ X6)
% 25.51/25.69          | (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X5 @ X7)) @ X6))),
% 25.51/25.69      inference('demod', [status(thm)], ['16', '17'])).
% 25.51/25.69  thf('19', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i]:
% 25.51/25.69         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 25.51/25.69      inference('sup-', [status(thm)], ['15', '18'])).
% 25.51/25.69  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 25.51/25.69      inference('simplify', [status(thm)], ['14'])).
% 25.51/25.69  thf(t110_xboole_1, axiom,
% 25.51/25.69    (![A:$i,B:$i,C:$i]:
% 25.51/25.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 25.51/25.69       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 25.51/25.69  thf('21', plain,
% 25.51/25.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.51/25.69         (~ (r1_tarski @ X8 @ X9)
% 25.51/25.69          | ~ (r1_tarski @ X10 @ X9)
% 25.51/25.69          | (r1_tarski @ (k5_xboole_0 @ X8 @ X10) @ X9))),
% 25.51/25.69      inference('cnf', [status(esa)], [t110_xboole_1])).
% 25.51/25.69  thf('22', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i]:
% 25.51/25.69         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 25.51/25.69      inference('sup-', [status(thm)], ['20', '21'])).
% 25.51/25.69  thf('23', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i]:
% 25.51/25.69         (r1_tarski @ 
% 25.51/25.69          (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X0)),
% 25.51/25.69      inference('sup-', [status(thm)], ['19', '22'])).
% 25.51/25.69  thf(t100_xboole_1, axiom,
% 25.51/25.69    (![A:$i,B:$i]:
% 25.51/25.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 25.51/25.69  thf('24', plain,
% 25.51/25.69      (![X3 : $i, X4 : $i]:
% 25.51/25.69         ((k4_xboole_0 @ X3 @ X4)
% 25.51/25.69           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 25.51/25.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.51/25.69  thf('25', plain,
% 25.51/25.69      (![X50 : $i, X51 : $i]:
% 25.51/25.69         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 25.51/25.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 25.51/25.69  thf('26', plain,
% 25.51/25.69      (![X3 : $i, X4 : $i]:
% 25.51/25.69         ((k4_xboole_0 @ X3 @ X4)
% 25.51/25.69           = (k5_xboole_0 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 25.51/25.69      inference('demod', [status(thm)], ['24', '25'])).
% 25.51/25.69  thf('27', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 25.51/25.69      inference('demod', [status(thm)], ['23', '26'])).
% 25.51/25.69  thf(t1_xboole_1, axiom,
% 25.51/25.69    (![A:$i,B:$i,C:$i]:
% 25.51/25.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 25.51/25.69       ( r1_tarski @ A @ C ) ))).
% 25.51/25.69  thf('28', plain,
% 25.51/25.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.51/25.69         (~ (r1_tarski @ X11 @ X12)
% 25.51/25.69          | ~ (r1_tarski @ X12 @ X13)
% 25.51/25.69          | (r1_tarski @ X11 @ X13))),
% 25.51/25.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 25.51/25.69  thf('29', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.51/25.69         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 25.51/25.69      inference('sup-', [status(thm)], ['27', '28'])).
% 25.51/25.69  thf('30', plain,
% 25.51/25.69      (![X0 : $i]:
% 25.51/25.69         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 25.51/25.69          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 25.51/25.69      inference('sup-', [status(thm)], ['13', '29'])).
% 25.51/25.69  thf('31', plain,
% 25.51/25.69      (![X41 : $i, X42 : $i, X43 : $i]:
% 25.51/25.69         (~ (r1_tarski @ X41 @ X42)
% 25.51/25.69          | (r2_hidden @ X41 @ X43)
% 25.51/25.69          | ((X43) != (k1_zfmisc_1 @ X42)))),
% 25.51/25.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 25.51/25.69  thf('32', plain,
% 25.51/25.69      (![X41 : $i, X42 : $i]:
% 25.51/25.69         ((r2_hidden @ X41 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X41 @ X42))),
% 25.51/25.69      inference('simplify', [status(thm)], ['31'])).
% 25.51/25.69  thf('33', plain,
% 25.51/25.69      (![X0 : $i]:
% 25.51/25.69         (r2_hidden @ (k4_xboole_0 @ sk_B @ X0) @ 
% 25.51/25.69          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 25.51/25.69      inference('sup-', [status(thm)], ['30', '32'])).
% 25.51/25.69  thf(t1_subset, axiom,
% 25.51/25.69    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 25.51/25.69  thf('34', plain,
% 25.51/25.69      (![X52 : $i, X53 : $i]:
% 25.51/25.69         ((m1_subset_1 @ X52 @ X53) | ~ (r2_hidden @ X52 @ X53))),
% 25.51/25.69      inference('cnf', [status(esa)], [t1_subset])).
% 25.51/25.69  thf('35', plain,
% 25.51/25.69      (![X0 : $i]:
% 25.51/25.69         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 25.51/25.69          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 25.51/25.69      inference('sup-', [status(thm)], ['33', '34'])).
% 25.51/25.69  thf(t18_tops_2, axiom,
% 25.51/25.69    (![A:$i]:
% 25.51/25.69     ( ( l1_pre_topc @ A ) =>
% 25.51/25.69       ( ![B:$i]:
% 25.51/25.69         ( ( m1_subset_1 @
% 25.51/25.69             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 25.51/25.69           ( ![C:$i]:
% 25.51/25.69             ( ( m1_subset_1 @
% 25.51/25.69                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 25.51/25.69               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 25.51/25.69                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 25.51/25.69  thf('36', plain,
% 25.51/25.69      (![X56 : $i, X57 : $i, X58 : $i]:
% 25.51/25.69         (~ (m1_subset_1 @ X56 @ 
% 25.51/25.69             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57))))
% 25.51/25.69          | (v1_tops_2 @ X56 @ X57)
% 25.51/25.69          | ~ (r1_tarski @ X56 @ X58)
% 25.51/25.69          | ~ (v1_tops_2 @ X58 @ X57)
% 25.51/25.69          | ~ (m1_subset_1 @ X58 @ 
% 25.51/25.69               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57))))
% 25.51/25.69          | ~ (l1_pre_topc @ X57))),
% 25.51/25.69      inference('cnf', [status(esa)], [t18_tops_2])).
% 25.51/25.69  thf('37', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i]:
% 25.51/25.69         (~ (l1_pre_topc @ sk_A)
% 25.51/25.69          | ~ (m1_subset_1 @ X1 @ 
% 25.51/25.69               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 25.51/25.69          | ~ (v1_tops_2 @ X1 @ sk_A)
% 25.51/25.69          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 25.51/25.69          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 25.51/25.69      inference('sup-', [status(thm)], ['35', '36'])).
% 25.51/25.69  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 25.51/25.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.51/25.69  thf('39', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i]:
% 25.51/25.69         (~ (m1_subset_1 @ X1 @ 
% 25.51/25.69             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 25.51/25.69          | ~ (v1_tops_2 @ X1 @ sk_A)
% 25.51/25.69          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 25.51/25.69          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 25.51/25.69      inference('demod', [status(thm)], ['37', '38'])).
% 25.51/25.69  thf('40', plain,
% 25.51/25.69      (![X0 : $i]:
% 25.51/25.69         ((v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 25.51/25.69          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 25.51/25.69          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 25.51/25.69      inference('sup-', [status(thm)], ['5', '39'])).
% 25.51/25.69  thf('41', plain,
% 25.51/25.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 25.51/25.69      inference('demod', [status(thm)], ['23', '26'])).
% 25.51/25.69  thf('42', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 25.51/25.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.51/25.69  thf('43', plain,
% 25.51/25.69      (![X0 : $i]: (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 25.51/25.69      inference('demod', [status(thm)], ['40', '41', '42'])).
% 25.51/25.69  thf('44', plain, ($false), inference('demod', [status(thm)], ['4', '43'])).
% 25.51/25.69  
% 25.51/25.69  % SZS output end Refutation
% 25.51/25.69  
% 25.51/25.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
