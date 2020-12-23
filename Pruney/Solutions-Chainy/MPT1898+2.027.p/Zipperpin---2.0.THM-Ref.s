%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FBjsvaLXZ5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:42 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 168 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :   19
%              Number of atoms          :  503 (1456 expanded)
%              Number of equality atoms :    7 (  28 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t66_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ? [B: $i] :
            ( ( v3_tex_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tex_2])).

thf('1',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X18: $i] :
      ( ~ ( v3_tex_2 @ X18 @ sk_A )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( v3_tex_2 @ ( sk_C @ X16 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ X1 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['34','46'])).

thf('48',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FBjsvaLXZ5
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:00:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 380 iterations in 0.179s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.44/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.62  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.44/0.62  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.62  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.62  thf(t66_tex_2, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.44/0.62         ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ?[B:$i]:
% 0.44/0.62         ( ( v3_tex_2 @ B @ A ) & 
% 0.44/0.62           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.62            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62          ( ?[B:$i]:
% 0.44/0.62            ( ( v3_tex_2 @ B @ A ) & 
% 0.44/0.62              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.44/0.62  thf('1', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t9_mcart_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ~( ( r2_hidden @ B @ A ) & 
% 0.44/0.62                 ( ![C:$i,D:$i]:
% 0.44/0.62                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.44/0.62                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X11 : $i]:
% 0.44/0.62         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.44/0.62      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.44/0.62  thf(t36_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.44/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.62  thf(t3_subset, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      (![X5 : $i, X7 : $i]:
% 0.44/0.62         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.62  thf(t5_subset, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.44/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X8 @ X9)
% 0.44/0.62          | ~ (v1_xboole_0 @ X10)
% 0.44/0.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['2', '7'])).
% 0.44/0.62  thf(l32_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.44/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62          | ~ (v1_xboole_0 @ X1)
% 0.44/0.62          | (r1_tarski @ X1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X1 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X5 : $i, X7 : $i]:
% 0.44/0.62         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.62  thf(t35_tex_2, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( ( v1_xboole_0 @ B ) & 
% 0.44/0.62             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X14 : $i, X15 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X14)
% 0.44/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.44/0.62          | (v2_tex_2 @ X14 @ X15)
% 0.44/0.62          | ~ (l1_pre_topc @ X15)
% 0.44/0.62          | ~ (v2_pre_topc @ X15)
% 0.44/0.62          | (v2_struct_0 @ X15))),
% 0.44/0.62      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X1)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | (v2_tex_2 @ X1 @ X0)
% 0.44/0.62          | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_tex_2 @ X1 @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (v1_xboole_0 @ X1))),
% 0.44/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0)
% 0.44/0.62          | (v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62          | (v2_tex_2 @ X0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '16'])).
% 0.44/0.62  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0) | (v2_struct_0 @ sk_A) | (v2_tex_2 @ X0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      (![X0 : $i]: ((v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('clc', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.62  thf(t65_tex_2, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.44/0.62         ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.44/0.62                ( ![C:$i]:
% 0.44/0.62                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.62          | ~ (v2_tex_2 @ X16 @ X17)
% 0.44/0.62          | (m1_subset_1 @ (sk_C @ X16 @ X17) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.62          | ~ (l1_pre_topc @ X17)
% 0.44/0.62          | ~ (v3_tdlat_3 @ X17)
% 0.44/0.62          | ~ (v2_pre_topc @ X17)
% 0.44/0.62          | (v2_struct_0 @ X17))),
% 0.44/0.62      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X1)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (v3_tdlat_3 @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | (m1_subset_1 @ (sk_C @ X1 @ X0) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.44/0.62          | ~ (v2_tex_2 @ X1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0)
% 0.44/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62          | ~ (v3_tdlat_3 @ sk_A)
% 0.44/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62          | (v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['21', '24'])).
% 0.44/0.62  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('27', plain, ((v3_tdlat_3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0)
% 0.44/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | (v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.44/0.62  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0)
% 0.44/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('clc', [status(thm)], ['30', '31'])).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      (![X18 : $i]:
% 0.44/0.62         (~ (v3_tex_2 @ X18 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0) | ~ (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (![X0 : $i]: ((v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('clc', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.62          | ~ (v2_tex_2 @ X16 @ X17)
% 0.44/0.62          | (v3_tex_2 @ (sk_C @ X16 @ X17) @ X17)
% 0.44/0.62          | ~ (l1_pre_topc @ X17)
% 0.44/0.62          | ~ (v3_tdlat_3 @ X17)
% 0.44/0.62          | ~ (v2_pre_topc @ X17)
% 0.44/0.62          | (v2_struct_0 @ X17))),
% 0.44/0.62      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X1)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (v3_tdlat_3 @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | (v3_tex_2 @ (sk_C @ X1 @ X0) @ X0)
% 0.44/0.62          | ~ (v2_tex_2 @ X1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0)
% 0.44/0.62          | (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 0.44/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62          | ~ (v3_tdlat_3 @ sk_A)
% 0.44/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62          | (v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['35', '38'])).
% 0.44/0.62  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('41', plain, ((v3_tdlat_3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0)
% 0.44/0.62          | (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 0.44/0.62          | (v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 0.44/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.44/0.62  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ X0) | (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A))),
% 0.44/0.62      inference('clc', [status(thm)], ['44', '45'])).
% 0.44/0.62  thf('47', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.44/0.62      inference('clc', [status(thm)], ['34', '46'])).
% 0.44/0.62  thf('48', plain, ($false), inference('sup-', [status(thm)], ['0', '47'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
