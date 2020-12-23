%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZFoRudu9iy

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:30 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 147 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  502 (1133 expanded)
%              Number of equality atoms :   32 (  51 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('19',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('20',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X21 )
       != ( sk_C @ X18 @ X19 ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['22','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('48',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('53',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','37','53'])).

thf('55',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['4','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZFoRudu9iy
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 1007 iterations in 0.537s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.75/0.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/0.98  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.75/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.98  thf(t35_tex_2, conjecture,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( ( v1_xboole_0 @ B ) & 
% 0.75/0.98             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.75/0.98           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i]:
% 0.75/0.98        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/0.98            ( l1_pre_topc @ A ) ) =>
% 0.75/0.98          ( ![B:$i]:
% 0.75/0.98            ( ( ( v1_xboole_0 @ B ) & 
% 0.75/0.98                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.75/0.98              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.75/0.98  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(l13_xboole_0, axiom,
% 0.75/0.98    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.75/0.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.98  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.98  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.75/0.98      inference('demod', [status(thm)], ['0', '3'])).
% 0.75/0.98  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.75/0.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.98  thf(t4_subset_1, axiom,
% 0.75/0.98    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.75/0.98  thf('7', plain,
% 0.75/0.98      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.75/0.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.75/0.98  thf(cc2_pre_topc, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.75/0.98          | (v4_pre_topc @ X16 @ X17)
% 0.75/0.98          | ~ (v1_xboole_0 @ X16)
% 0.75/0.98          | ~ (l1_pre_topc @ X17)
% 0.75/0.98          | ~ (v2_pre_topc @ X17))),
% 0.75/0.98      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (v2_pre_topc @ X0)
% 0.75/0.98          | ~ (l1_pre_topc @ X0)
% 0.75/0.98          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.98          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.98  thf('10', plain, ((v1_xboole_0 @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.98  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.98      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (v2_pre_topc @ X0)
% 0.75/0.98          | ~ (l1_pre_topc @ X0)
% 0.75/0.98          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['9', '12'])).
% 0.75/0.98  thf('14', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((v4_pre_topc @ X0 @ X1)
% 0.75/0.98          | ~ (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (l1_pre_topc @ X1)
% 0.75/0.98          | ~ (v2_pre_topc @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['6', '13'])).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (v2_pre_topc @ sk_A)
% 0.75/0.98          | ~ (v1_xboole_0 @ X0)
% 0.75/0.98          | (v4_pre_topc @ X0 @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['5', '14'])).
% 0.75/0.98  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['15', '16'])).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.75/0.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.75/0.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.75/0.98  thf(d6_tex_2, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( l1_pre_topc @ A ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98           ( ( v2_tex_2 @ B @ A ) <=>
% 0.75/0.98             ( ![C:$i]:
% 0.75/0.98               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.75/0.98                      ( ![D:$i]:
% 0.75/0.98                        ( ( m1_subset_1 @
% 0.75/0.98                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.98                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.75/0.98                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.75/0.98                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('20', plain,
% 0.75/0.98      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/0.98          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/0.98          | ~ (v4_pre_topc @ X21 @ X19)
% 0.75/0.98          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X21)
% 0.75/0.98              != (sk_C @ X18 @ X19))
% 0.75/0.98          | (v2_tex_2 @ X18 @ X19)
% 0.75/0.98          | ~ (l1_pre_topc @ X19))),
% 0.75/0.98      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.75/0.98  thf('21', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.75/0.98          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.75/0.98              != (sk_C @ k1_xboole_0 @ X0))
% 0.75/0.98          | ~ (v4_pre_topc @ X1 @ X0)
% 0.75/0.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.75/0.98          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.98              != (sk_C @ k1_xboole_0 @ X0))
% 0.75/0.98          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.75/0.98          | ~ (l1_pre_topc @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['18', '21'])).
% 0.75/0.98  thf('23', plain,
% 0.75/0.98      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.75/0.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.75/0.98  thf(redefinition_k9_subset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.98       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.98         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.75/0.98          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.75/0.98      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.75/0.98  thf('25', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.75/0.98           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['23', '24'])).
% 0.75/0.98  thf(t48_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      (![X7 : $i, X8 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.75/0.98           = (k3_xboole_0 @ X7 @ X8))),
% 0.75/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.98  thf(t36_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.75/0.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.75/0.98  thf(t3_xboole_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.98  thf('28', plain,
% 0.75/0.98      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.75/0.98  thf('29', plain,
% 0.75/0.98      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['27', '28'])).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['26', '29'])).
% 0.75/0.98  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.98      inference('demod', [status(thm)], ['25', '32'])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.75/0.98          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.75/0.98          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.75/0.98          | ~ (l1_pre_topc @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['22', '33'])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.75/0.98        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['17', '34'])).
% 0.75/0.98  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.98      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.75/0.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.75/0.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['38', '39'])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      (![X18 : $i, X19 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/0.98          | (r1_tarski @ (sk_C @ X18 @ X19) @ X18)
% 0.75/0.98          | (v2_tex_2 @ X18 @ X19)
% 0.75/0.98          | ~ (l1_pre_topc @ X19))),
% 0.75/0.98      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.75/0.98  thf('42', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_xboole_0 @ X1)
% 0.75/0.98          | ~ (l1_pre_topc @ X0)
% 0.75/0.98          | (v2_tex_2 @ X1 @ X0)
% 0.75/0.98          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['40', '41'])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.75/0.98  thf('44', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.75/0.98          | ~ (l1_pre_topc @ X0)
% 0.75/0.98          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.98          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['42', '43'])).
% 0.75/0.98  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.98      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf('46', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.75/0.98          | ~ (l1_pre_topc @ X0)
% 0.75/0.98          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['44', '45'])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.75/0.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.98  thf('48', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.75/0.98      inference('demod', [status(thm)], ['0', '3'])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('50', plain,
% 0.75/0.98      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.75/0.98        | ~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['46', '49'])).
% 0.75/0.98  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.98      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf('53', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.75/0.98      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.75/0.98  thf('54', plain,
% 0.75/0.98      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['35', '36', '37', '53'])).
% 0.75/0.98  thf('55', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.75/0.98      inference('simplify', [status(thm)], ['54'])).
% 0.75/0.98  thf('56', plain, ($false), inference('demod', [status(thm)], ['4', '55'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
