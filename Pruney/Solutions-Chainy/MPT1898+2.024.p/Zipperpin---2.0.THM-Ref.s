%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YMdJIQFnMO

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 125 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  470 (1084 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_2_0_compts_1_type,type,(
    o_2_0_compts_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_o_2_0_compts_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( o_2_0_compts_1 @ A @ B ) @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( o_2_0_compts_1 @ X11 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_0_compts_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( o_2_0_compts_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( o_2_0_compts_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( o_2_0_compts_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( v3_tex_2 @ ( sk_C @ X15 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','18'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_C @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X17: $i] :
      ( ~ ( v3_tex_2 @ X17 @ sk_A )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YMdJIQFnMO
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 33 iterations in 0.018s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(o_2_0_compts_1_type, type, o_2_0_compts_1: $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.46  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(t66_tex_2, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.46         ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ?[B:$i]:
% 0.20/0.46         ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.46           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.46            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46          ( ?[B:$i]:
% 0.20/0.46            ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.46              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.20/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t4_subset_1, axiom,
% 0.20/0.46    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.46  thf(t35_tex_2, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.46             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.46           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ X13)
% 0.20/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.46          | (v2_tex_2 @ X13 @ X14)
% 0.20/0.46          | ~ (l1_pre_topc @ X14)
% 0.20/0.46          | ~ (v2_pre_topc @ X14)
% 0.20/0.46          | (v2_struct_0 @ X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.46          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.46  thf(dt_o_2_0_compts_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.46       ( m1_subset_1 @ ( o_2_0_compts_1 @ A @ B ) @ B ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X11)
% 0.20/0.46          | ~ (v2_pre_topc @ X11)
% 0.20/0.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.46          | (m1_subset_1 @ (o_2_0_compts_1 @ X11 @ X12) @ X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_o_2_0_compts_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((m1_subset_1 @ (o_2_0_compts_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf(t2_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         ((r2_hidden @ X1 @ X2)
% 0.20/0.46          | (v1_xboole_0 @ X2)
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.46          | (r2_hidden @ (o_2_0_compts_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf(t7_ordinal1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v1_xboole_0 @ k1_xboole_0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | ~ (r1_tarski @ k1_xboole_0 @ (o_2_0_compts_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.46  thf(t3_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.46  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v1_xboole_0 @ k1_xboole_0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.46  thf('16', plain, ((~ (v2_pre_topc @ sk_A) | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.46  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.46  thf(t65_tex_2, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.46         ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.46                ( ![C:$i]:
% 0.20/0.46                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X15 : $i, X16 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.46          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.46          | (v3_tex_2 @ (sk_C @ X15 @ X16) @ X16)
% 0.20/0.46          | ~ (l1_pre_topc @ X16)
% 0.20/0.46          | ~ (v3_tdlat_3 @ X16)
% 0.20/0.46          | ~ (v2_pre_topc @ X16)
% 0.20/0.46          | (v2_struct_0 @ X16))),
% 0.20/0.46      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.46          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | (v2_struct_0 @ X0)
% 0.20/0.46          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | (v2_struct_0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v3_tdlat_3 @ X0)
% 0.20/0.46          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.46          | (v2_struct_0 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '18'])).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X15 : $i, X16 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.46          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.46          | (m1_subset_1 @ (sk_C @ X15 @ X16) @ 
% 0.20/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.46          | ~ (l1_pre_topc @ X16)
% 0.20/0.46          | ~ (v3_tdlat_3 @ X16)
% 0.20/0.46          | ~ (v2_pre_topc @ X16)
% 0.20/0.46          | (v2_struct_0 @ X16))),
% 0.20/0.46      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.20/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.46          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | (v2_struct_0 @ X0)
% 0.20/0.46          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.20/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | (v2_struct_0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v3_tdlat_3 @ X0)
% 0.20/0.46          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.20/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.46          | (v2_struct_0 @ X0)
% 0.20/0.46          | ~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (![X17 : $i]:
% 0.20/0.46         (~ (v3_tex_2 @ X17 @ sk_A)
% 0.20/0.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | (v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.46        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.46  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('35', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.46  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('38', plain, (~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.20/0.46      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46        | (v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '38'])).
% 0.20/0.46  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('42', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('43', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.20/0.46  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
