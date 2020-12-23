%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c4arYk7LhC

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:29 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 128 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  493 ( 993 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
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

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('6',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('30',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X20 )
       != ( sk_C @ X17 @ X18 ) )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X2 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['32','45'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('52',plain,(
    k1_xboole_0
 != ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c4arYk7LhC
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 198 iterations in 0.178s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.67  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(t4_subset_1, axiom,
% 0.46/0.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf(d5_tex_2, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67           ( ( v2_tex_2 @ B @ A ) <=>
% 0.46/0.67             ( ![C:$i]:
% 0.46/0.67               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.46/0.67                      ( ![D:$i]:
% 0.46/0.67                        ( ( m1_subset_1 @
% 0.46/0.67                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.67                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.46/0.67                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.67          | (r1_tarski @ (sk_C @ X17 @ X18) @ X17)
% 0.46/0.67          | (v2_tex_2 @ X17 @ X18)
% 0.46/0.67          | ~ (l1_pre_topc @ X18))),
% 0.46/0.67      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (l1_pre_topc @ X0)
% 0.46/0.67          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.67          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf(t3_xboole_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf(l13_xboole_0, axiom,
% 0.46/0.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.67  thf(t35_tex_2, conjecture,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( v1_xboole_0 @ B ) & 
% 0.46/0.67             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.67           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i]:
% 0.46/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.67            ( l1_pre_topc @ A ) ) =>
% 0.46/0.67          ( ![B:$i]:
% 0.46/0.67            ( ( ( v1_xboole_0 @ B ) & 
% 0.46/0.67                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.67              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.46/0.67  thf('6', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('7', plain, ((v1_xboole_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.67  thf('9', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf('10', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.46/0.67      inference('demod', [status(thm)], ['6', '9'])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['5', '10'])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.46/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.67        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['4', '11'])).
% 0.46/0.67  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('14', plain, ((v1_xboole_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('15', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.67  thf('17', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.46/0.67      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.46/0.67  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.67  thf(cc1_tops_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.46/0.67          | (v3_pre_topc @ X15 @ X16)
% 0.46/0.67          | ~ (v1_xboole_0 @ X15)
% 0.46/0.67          | ~ (l1_pre_topc @ X16)
% 0.46/0.67          | ~ (v2_pre_topc @ X16))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X1)
% 0.46/0.67          | ~ (v2_pre_topc @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | ~ (v1_xboole_0 @ X1)
% 0.46/0.67          | (v3_pre_topc @ X1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((v3_pre_topc @ X1 @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | ~ (v2_pre_topc @ X0)
% 0.46/0.67          | ~ (v1_xboole_0 @ X1))),
% 0.46/0.67      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X0)
% 0.46/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.67          | (v3_pre_topc @ X0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '24'])).
% 0.46/0.67  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.67          | ~ (v3_pre_topc @ X20 @ X18)
% 0.46/0.67          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X20)
% 0.46/0.67              != (sk_C @ X17 @ X18))
% 0.46/0.67          | (v2_tex_2 @ X17 @ X18)
% 0.46/0.67          | ~ (l1_pre_topc @ X18))),
% 0.46/0.67      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (l1_pre_topc @ X0)
% 0.46/0.67          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.67          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.46/0.67              != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.67          | ~ (v3_pre_topc @ X1 @ X0)
% 0.46/0.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.46/0.67          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.46/0.67              != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.67          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['28', '31'])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf(redefinition_k9_subset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.67       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.67         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.46/0.67          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.46/0.67           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf(dt_k9_subset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.67       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (k9_subset_1 @ X2 @ X3 @ X4) @ (k1_zfmisc_1 @ X2))
% 0.46/0.67          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X2)))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ 
% 0.46/0.67          (k1_zfmisc_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.67  thf(t3_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (![X9 : $i, X10 : $i]:
% 0.46/0.67         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ X0)),
% 0.46/0.67      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.67  thf('41', plain,
% 0.46/0.67      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.46/0.67           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('demod', [status(thm)], ['35', '44'])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.46/0.67          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.67          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['32', '45'])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.67        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.46/0.67        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['27', '46'])).
% 0.46/0.67  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.67  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('50', plain,
% 0.46/0.67      (((v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.46/0.67        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.46/0.67  thf('51', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.46/0.67      inference('demod', [status(thm)], ['6', '9'])).
% 0.46/0.67  thf('52', plain, (((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.46/0.67  thf('53', plain, ($false),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['17', '52'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
