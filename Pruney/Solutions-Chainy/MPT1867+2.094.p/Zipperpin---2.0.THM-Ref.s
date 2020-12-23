%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yAhPHiBB96

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:39 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 129 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  505 ( 979 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('22',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X20 )
       != ( sk_C @ X17 @ X18 ) )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['25','28','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','34'])).

thf('36',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('51',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38','39','51'])).

thf('53',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yAhPHiBB96
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.59/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.81  % Solved by: fo/fo7.sh
% 0.59/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.81  % done 893 iterations in 0.341s
% 0.59/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.81  % SZS output start Refutation
% 0.59/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.81  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.59/0.81  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.59/0.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.81  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.59/0.81  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.59/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.81  thf(t35_tex_2, conjecture,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( ( v1_xboole_0 @ B ) & 
% 0.59/0.81             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.81           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.81    (~( ![A:$i]:
% 0.59/0.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.81            ( l1_pre_topc @ A ) ) =>
% 0.59/0.81          ( ![B:$i]:
% 0.59/0.81            ( ( ( v1_xboole_0 @ B ) & 
% 0.59/0.81                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.81              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.59/0.81  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(l13_xboole_0, axiom,
% 0.59/0.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.81  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.59/0.81      inference('demod', [status(thm)], ['0', '3'])).
% 0.59/0.81  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('6', plain,
% 0.59/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.81  thf(t4_subset_1, axiom,
% 0.59/0.81    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.59/0.81  thf('7', plain,
% 0.59/0.81      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.81  thf(t44_tops_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_pre_topc @ A ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.59/0.81  thf('8', plain,
% 0.59/0.81      (![X15 : $i, X16 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.59/0.81          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ X15)
% 0.59/0.81          | ~ (l1_pre_topc @ X16))),
% 0.59/0.81      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.59/0.81  thf('9', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X0)
% 0.59/0.81          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.81  thf(t3_xboole_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.81  thf('10', plain,
% 0.59/0.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X0)
% 0.59/0.81          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.81  thf('12', plain,
% 0.59/0.81      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.81  thf(fc9_tops_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.59/0.81         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.81       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      (![X13 : $i, X14 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X13)
% 0.59/0.81          | ~ (v2_pre_topc @ X13)
% 0.59/0.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.59/0.81          | (v3_pre_topc @ (k1_tops_1 @ X13 @ X14) @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v3_pre_topc @ (k1_tops_1 @ X0 @ k1_xboole_0) @ X0)
% 0.59/0.81          | ~ (v2_pre_topc @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0)
% 0.59/0.81          | ~ (v2_pre_topc @ X0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['11', '14'])).
% 0.59/0.81  thf('16', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v2_pre_topc @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0)
% 0.59/0.81          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.59/0.81      inference('simplify', [status(thm)], ['15'])).
% 0.59/0.81  thf('17', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v3_pre_topc @ X0 @ X1)
% 0.59/0.81          | ~ (v1_xboole_0 @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1))),
% 0.59/0.81      inference('sup+', [status(thm)], ['6', '16'])).
% 0.59/0.81  thf('18', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v2_pre_topc @ sk_A)
% 0.59/0.81          | ~ (v1_xboole_0 @ X0)
% 0.59/0.81          | (v3_pre_topc @ X0 @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['5', '17'])).
% 0.59/0.81  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('20', plain,
% 0.59/0.81      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['18', '19'])).
% 0.59/0.81  thf('21', plain,
% 0.59/0.81      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.81  thf('22', plain,
% 0.59/0.81      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.81  thf(d5_tex_2, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_pre_topc @ A ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( ( v2_tex_2 @ B @ A ) <=>
% 0.59/0.81             ( ![C:$i]:
% 0.59/0.81               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.59/0.81                      ( ![D:$i]:
% 0.59/0.81                        ( ( m1_subset_1 @
% 0.59/0.81                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.59/0.81                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.59/0.81                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.81  thf('23', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.81          | ~ (v3_pre_topc @ X20 @ X18)
% 0.59/0.81          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X20)
% 0.59/0.81              != (sk_C @ X17 @ X18))
% 0.59/0.81          | (v2_tex_2 @ X17 @ X18)
% 0.59/0.81          | ~ (l1_pre_topc @ X18))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.59/0.81  thf('24', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X0)
% 0.59/0.81          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.59/0.81          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.59/0.81              != (sk_C @ k1_xboole_0 @ X0))
% 0.59/0.81          | ~ (v3_pre_topc @ X1 @ X0)
% 0.59/0.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.81  thf('25', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.59/0.81          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.59/0.81              != (sk_C @ k1_xboole_0 @ X0))
% 0.59/0.81          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['21', '24'])).
% 0.59/0.81  thf('26', plain,
% 0.59/0.81      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.81  thf(redefinition_k9_subset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.81       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.81  thf('27', plain,
% 0.59/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.81         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.59/0.81          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.59/0.81  thf('28', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.59/0.81           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.81  thf(t48_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.81  thf('29', plain,
% 0.59/0.81      (![X4 : $i, X5 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.59/0.81           = (k3_xboole_0 @ X4 @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.81  thf(t36_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      (![X1 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ X1)),
% 0.59/0.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.81  thf('31', plain,
% 0.59/0.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.59/0.81  thf('32', plain,
% 0.59/0.81      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['29', '32'])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.59/0.81          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.59/0.81          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['25', '28', '33'])).
% 0.59/0.81  thf('35', plain,
% 0.59/0.81      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.81        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.59/0.81        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['20', '34'])).
% 0.59/0.81  thf('36', plain, ((v1_xboole_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('37', plain, (((sk_B) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.81      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.81  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('40', plain,
% 0.59/0.81      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.81  thf('41', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.81          | (r1_tarski @ (sk_C @ X17 @ X18) @ X17)
% 0.59/0.81          | (v2_tex_2 @ X17 @ X18)
% 0.59/0.81          | ~ (l1_pre_topc @ X18))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.59/0.81  thf('42', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X0)
% 0.59/0.81          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.59/0.81          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.81  thf('43', plain,
% 0.59/0.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.59/0.81  thf('44', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0)
% 0.59/0.81          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.81  thf('45', plain,
% 0.59/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.81  thf('46', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.59/0.81      inference('demod', [status(thm)], ['0', '3'])).
% 0.59/0.81  thf('47', plain,
% 0.59/0.81      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.81  thf('48', plain,
% 0.59/0.81      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.59/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.81        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['44', '47'])).
% 0.59/0.81  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.81      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.81  thf('51', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.59/0.81  thf('52', plain,
% 0.59/0.81      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['35', '38', '39', '51'])).
% 0.59/0.81  thf('53', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.59/0.81      inference('simplify', [status(thm)], ['52'])).
% 0.59/0.81  thf('54', plain, ($false), inference('demod', [status(thm)], ['4', '53'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
