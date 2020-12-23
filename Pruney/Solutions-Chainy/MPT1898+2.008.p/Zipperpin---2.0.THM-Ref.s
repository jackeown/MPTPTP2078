%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z0PilSjJv1

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 159 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   19
%              Number of atoms          :  549 (1324 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('13',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k1_tops_1 @ X13 @ X12 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_tops_1 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(fc13_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_tops_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v1_xboole_0 @ ( k1_tops_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_tops_1 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_tops_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','25'])).

thf('27',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( v3_tex_2 @ ( sk_C @ X16 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','25'])).

thf('33',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X18: $i] :
      ( ~ ( v3_tex_2 @ X18 @ sk_A )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z0PilSjJv1
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 38 iterations in 0.015s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.47  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.47  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.47  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.22/0.47  thf(t66_tex_2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.22/0.47         ( l1_pre_topc @ A ) ) =>
% 0.22/0.47       ( ?[B:$i]:
% 0.22/0.47         ( ( v3_tex_2 @ B @ A ) & 
% 0.22/0.47           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.47            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.47          ( ?[B:$i]:
% 0.22/0.47            ( ( v3_tex_2 @ B @ A ) & 
% 0.22/0.47              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.22/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t4_subset_1, axiom,
% 0.22/0.47    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.47  thf(t35_tex_2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( ( v1_xboole_0 @ B ) & 
% 0.22/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X14 : $i, X15 : $i]:
% 0.22/0.47         (~ (v1_xboole_0 @ X14)
% 0.22/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.47          | (v2_tex_2 @ X14 @ X15)
% 0.22/0.47          | ~ (l1_pre_topc @ X15)
% 0.22/0.47          | ~ (v2_pre_topc @ X15)
% 0.22/0.47          | (v2_struct_0 @ X15))),
% 0.22/0.47      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v2_struct_0 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.47          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.47  thf(t44_tops_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( l1_pre_topc @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X10 : $i, X11 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.47          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ X10)
% 0.22/0.47          | ~ (l1_pre_topc @ X11))),
% 0.22/0.47      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X0)
% 0.22/0.47          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.47  thf('8', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.47  thf(d10_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X0 : $i, X2 : $i]:
% 0.22/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X0)
% 0.22/0.47          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X0)
% 0.22/0.47          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.47  thf(t84_tops_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( l1_pre_topc @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.47             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      (![X12 : $i, X13 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.47          | ((k1_tops_1 @ X13 @ X12) != (k1_xboole_0))
% 0.22/0.47          | (v2_tops_1 @ X12 @ X13)
% 0.22/0.47          | ~ (l1_pre_topc @ X13))),
% 0.22/0.47      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v2_tops_1 @ k1_xboole_0 @ X0)
% 0.22/0.47          | ((k1_tops_1 @ X0 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v2_tops_1 @ k1_xboole_0 @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['12', '15'])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X0 : $i]: ((v2_tops_1 @ k1_xboole_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.47  thf(fc13_tops_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( l1_pre_topc @ A ) & ( v2_tops_1 @ B @ A ) & 
% 0.22/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47       ( v1_xboole_0 @ ( k1_tops_1 @ A @ B ) ) ))).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X8 : $i, X9 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X8)
% 0.22/0.47          | ~ (v2_tops_1 @ X9 @ X8)
% 0.22/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.47          | (v1_xboole_0 @ (k1_tops_1 @ X8 @ X9)))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc13_tops_1])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0))
% 0.22/0.47          | ~ (v2_tops_1 @ k1_xboole_0 @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['17', '20'])).
% 0.22/0.47  thf('22', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0)) | ~ (l1_pre_topc @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.47  thf('23', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ k1_xboole_0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['11', '22'])).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (![X0 : $i]: (~ (l1_pre_topc @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.47  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.47      inference('sup-', [status(thm)], ['4', '24'])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v2_struct_0 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '25'])).
% 0.22/0.47  thf('27', plain,
% 0.22/0.47      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.47  thf(t65_tex_2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.22/0.47         ( l1_pre_topc @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.47                ( ![C:$i]:
% 0.22/0.47                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf('28', plain,
% 0.22/0.47      (![X16 : $i, X17 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.47          | ~ (v2_tex_2 @ X16 @ X17)
% 0.22/0.47          | (v3_tex_2 @ (sk_C @ X16 @ X17) @ X17)
% 0.22/0.47          | ~ (l1_pre_topc @ X17)
% 0.22/0.47          | ~ (v3_tdlat_3 @ X17)
% 0.22/0.47          | ~ (v2_pre_topc @ X17)
% 0.22/0.47          | (v2_struct_0 @ X17))),
% 0.22/0.47      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v2_struct_0 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.22/0.47          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.47  thf('30', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | (v2_struct_0 @ X0)
% 0.22/0.47          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | (v2_struct_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.47  thf('31', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v3_tdlat_3 @ X0)
% 0.22/0.47          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.22/0.47          | (v2_struct_0 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.47  thf('32', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v2_struct_0 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '25'])).
% 0.22/0.47  thf('33', plain,
% 0.22/0.47      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.47  thf('34', plain,
% 0.22/0.47      (![X16 : $i, X17 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.47          | ~ (v2_tex_2 @ X16 @ X17)
% 0.22/0.47          | (m1_subset_1 @ (sk_C @ X16 @ X17) @ 
% 0.22/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.47          | ~ (l1_pre_topc @ X17)
% 0.22/0.47          | ~ (v3_tdlat_3 @ X17)
% 0.22/0.47          | ~ (v2_pre_topc @ X17)
% 0.22/0.47          | (v2_struct_0 @ X17))),
% 0.22/0.47      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.22/0.47  thf('35', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v2_struct_0 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.22/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.47          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.47  thf('36', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | (v2_struct_0 @ X0)
% 0.22/0.47          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.22/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | (v2_struct_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['32', '35'])).
% 0.22/0.47  thf('37', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v3_tdlat_3 @ X0)
% 0.22/0.47          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.22/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.47          | (v2_struct_0 @ X0)
% 0.22/0.47          | ~ (v2_pre_topc @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.47  thf('38', plain,
% 0.22/0.47      (![X18 : $i]:
% 0.22/0.47         (~ (v3_tex_2 @ X18 @ sk_A)
% 0.22/0.47          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('39', plain,
% 0.22/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.47        | (v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (v3_tdlat_3 @ sk_A)
% 0.22/0.47        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.47  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('42', plain, ((v3_tdlat_3 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('43', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.22/0.47  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('45', plain, (~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.22/0.47      inference('clc', [status(thm)], ['43', '44'])).
% 0.22/0.47  thf('46', plain,
% 0.22/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.47        | (v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (v3_tdlat_3 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['31', '45'])).
% 0.22/0.47  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('49', plain, ((v3_tdlat_3 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.47      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.22/0.47  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
