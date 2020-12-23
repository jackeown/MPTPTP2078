%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nYjzn5vcR0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:33 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 133 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  506 ( 944 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d6_tex_2,axiom,(
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
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X20 )
       != ( sk_C @ X17 @ X18 ) )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['23','36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','37'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40','52'])).

thf('54',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['4','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nYjzn5vcR0
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:23:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 266 iterations in 0.137s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(t35_tex_2, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( v1_xboole_0 @ B ) & 
% 0.39/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.58            ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ( v1_xboole_0 @ B ) & 
% 0.39/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.39/0.58  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(l13_xboole_0, axiom,
% 0.39/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.58  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.58  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.58  thf('7', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf(t3_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X12 : $i, X14 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf(cc2_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.58          | (v4_pre_topc @ X15 @ X16)
% 0.39/0.58          | ~ (v1_xboole_0 @ X15)
% 0.39/0.58          | ~ (l1_pre_topc @ X16)
% 0.39/0.58          | ~ (v2_pre_topc @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X1)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_xboole_0 @ X1)
% 0.39/0.58          | (v4_pre_topc @ X1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v4_pre_topc @ X1 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58          | (v4_pre_topc @ X0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '13'])).
% 0.39/0.58  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('17', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X12 : $i, X14 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf(d6_tex_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v2_tex_2 @ B @ A ) <=>
% 0.39/0.58             ( ![C:$i]:
% 0.39/0.58               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.39/0.58                      ( ![D:$i]:
% 0.39/0.58                        ( ( m1_subset_1 @
% 0.39/0.58                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.39/0.58                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.58                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.58          | ~ (v4_pre_topc @ X20 @ X18)
% 0.39/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X20)
% 0.39/0.58              != (sk_C @ X17 @ X18))
% 0.39/0.58          | (v2_tex_2 @ X17 @ X18)
% 0.39/0.58          | ~ (l1_pre_topc @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.39/0.58              != (sk_C @ k1_xboole_0 @ X0))
% 0.39/0.58          | ~ (v4_pre_topc @ X1 @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.39/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.39/0.58              != (sk_C @ k1_xboole_0 @ X0))
% 0.39/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf(redefinition_k9_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.58         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.39/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.39/0.58           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf(dt_k9_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.39/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ 
% 0.39/0.58          (k1_zfmisc_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i]:
% 0.39/0.58         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ X0)),
% 0.39/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.58  thf(t3_xboole_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.39/0.58           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '35'])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.39/0.58          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.39/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.39/0.58        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '37'])).
% 0.39/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.58  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.58          | (r1_tarski @ (sk_C @ X17 @ X18) @ X17)
% 0.39/0.58          | (v2_tex_2 @ X17 @ X18)
% 0.39/0.58          | ~ (l1_pre_topc @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.58  thf('47', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['45', '48'])).
% 0.39/0.58  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('52', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['38', '39', '40', '52'])).
% 0.39/0.58  thf('54', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.39/0.58      inference('simplify', [status(thm)], ['53'])).
% 0.39/0.58  thf('55', plain, ($false), inference('demod', [status(thm)], ['4', '54'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
