%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aAAmvfUDFA

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 117 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  504 (1088 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v1_tdlat_3 @ X7 )
      | ( v2_tex_2 @ X6 @ X7 )
      | ( X6
       != ( u1_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X7 ) @ X7 )
      | ~ ( v1_tdlat_3 @ X7 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X7 ) @ X7 )
      | ~ ( v1_tdlat_3 @ X7 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( X4
        = ( u1_struct_0 @ ( sk_C @ X4 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( r1_tarski @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ( v2_tex_2 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['36','46'])).

thf('48',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','47'])).

thf('49',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aAAmvfUDFA
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:31:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 59 iterations in 0.066s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(t43_tex_2, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.19/0.48         ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.48            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.19/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t27_tex_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.19/0.48             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.48          | ~ (v1_tdlat_3 @ X7)
% 0.19/0.48          | (v2_tex_2 @ X6 @ X7)
% 0.19/0.48          | ((X6) != (u1_struct_0 @ X7))
% 0.19/0.48          | ~ (l1_pre_topc @ X7)
% 0.19/0.48          | (v2_struct_0 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [t27_tex_2])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X7 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X7)
% 0.19/0.48          | ~ (l1_pre_topc @ X7)
% 0.19/0.48          | (v2_tex_2 @ (u1_struct_0 @ X7) @ X7)
% 0.19/0.48          | ~ (v1_tdlat_3 @ X7)
% 0.19/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.48  thf(dt_k2_subset_1, axiom,
% 0.19/0.48    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.48  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.48  thf('4', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.48  thf('5', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X7 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X7)
% 0.19/0.48          | ~ (l1_pre_topc @ X7)
% 0.19/0.48          | (v2_tex_2 @ (u1_struct_0 @ X7) @ X7)
% 0.19/0.48          | ~ (v1_tdlat_3 @ X7))),
% 0.19/0.48      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t10_tsep_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.48           ( ?[C:$i]:
% 0.19/0.48             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.19/0.48               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X4)
% 0.19/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.48          | ((X4) = (u1_struct_0 @ (sk_C @ X4 @ X5)))
% 0.19/0.48          | ~ (l1_pre_topc @ X5)
% 0.19/0.48          | (v2_struct_0 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B) | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.19/0.48      inference('clc', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X4)
% 0.19/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.48          | (m1_pre_topc @ (sk_C @ X4 @ X5) @ X5)
% 0.19/0.48          | ~ (l1_pre_topc @ X5)
% 0.19/0.48          | (v2_struct_0 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.48      inference('clc', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf(t35_borsuk_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.48           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (m1_pre_topc @ X2 @ X3)
% 0.19/0.48          | (r1_tarski @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X3))
% 0.19/0.48          | ~ (l1_pre_topc @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (r1_tarski @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.48           (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B)
% 0.19/0.48        | (r1_tarski @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.48           (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B) | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('28', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(t28_tex_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.19/0.48                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.48          | ~ (v2_tex_2 @ X8 @ X9)
% 0.19/0.48          | ~ (r1_tarski @ X10 @ X8)
% 0.19/0.48          | (v2_tex_2 @ X10 @ X9)
% 0.19/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.48          | ~ (l1_pre_topc @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.48          | (v2_tex_2 @ X1 @ X0)
% 0.19/0.48          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.48          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.48        | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.48        | (v2_tex_2 @ sk_B @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['27', '30'])).
% 0.19/0.48  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.48        | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.48        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      ((~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.48        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.48      inference('clc', [status(thm)], ['33', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B) | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '35'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t35_tex_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( v1_xboole_0 @ B ) & 
% 0.19/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.48           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X11)
% 0.19/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.48          | (v2_tex_2 @ X11 @ X12)
% 0.19/0.48          | ~ (l1_pre_topc @ X12)
% 0.19/0.48          | ~ (v2_pre_topc @ X12)
% 0.19/0.48          | (v2_struct_0 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (v2_tex_2 @ sk_B @ sk_A)
% 0.19/0.48        | ~ (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.48  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | (v2_tex_2 @ sk_B @ sk_A)
% 0.19/0.48        | ~ (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.19/0.48  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('44', plain, ((~ (v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.19/0.48      inference('clc', [status(thm)], ['42', '43'])).
% 0.19/0.48  thf('45', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('46', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('clc', [status(thm)], ['44', '45'])).
% 0.19/0.48  thf('47', plain, (~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.19/0.48      inference('clc', [status(thm)], ['36', '46'])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      ((~ (v1_tdlat_3 @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '47'])).
% 0.19/0.48  thf('49', plain, ((v1_tdlat_3 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('51', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.19/0.48  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
