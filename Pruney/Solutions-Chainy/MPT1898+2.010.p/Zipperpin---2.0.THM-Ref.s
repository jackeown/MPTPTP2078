%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l8XSzAURUs

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:39 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 141 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  518 (1132 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t58_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X21 ) @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t58_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('11',plain,
    ( ( sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
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

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ( v3_tex_2 @ ( sk_C_2 @ X22 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v3_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('27',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ( m1_subset_1 @ ( sk_C_2 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v3_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X24: $i] :
      ( ~ ( v3_tex_2 @ X24 @ sk_A )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_2 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_2 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v3_tex_2 @ ( sk_C_2 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l8XSzAURUs
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:48:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 134 iterations in 0.102s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.57  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.57  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.37/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.57  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.57  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.57  thf(t66_tex_2, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.37/0.57         ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ?[B:$i]:
% 0.37/0.57         ( ( v3_tex_2 @ B @ A ) & 
% 0.37/0.57           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.57            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57          ( ?[B:$i]:
% 0.37/0.57            ( ( v3_tex_2 @ B @ A ) & 
% 0.37/0.57              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.37/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t4_subset_1, axiom,
% 0.37/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf(t58_tex_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.37/0.57         ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( ![C:$i]:
% 0.37/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.57                 ( ( r2_hidden @ C @ B ) =>
% 0.37/0.57                   ( ( k9_subset_1 @
% 0.37/0.57                       ( u1_struct_0 @ A ) @ B @ 
% 0.37/0.57                       ( k2_pre_topc @
% 0.37/0.57                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.37/0.57                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.37/0.57             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.57          | (v2_tex_2 @ X20 @ X21)
% 0.37/0.57          | (r2_hidden @ (sk_C_1 @ X20 @ X21) @ X20)
% 0.37/0.57          | ~ (l1_pre_topc @ X21)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X21)
% 0.37/0.57          | ~ (v2_pre_topc @ X21)
% 0.37/0.57          | (v2_struct_0 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t58_tex_2])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v2_struct_0 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.37/0.57          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf(d1_xboole_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.57  thf(d1_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X7 @ X6)
% 0.37/0.57          | (r1_tarski @ X7 @ X5)
% 0.37/0.57          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X5 : $i, X7 : $i]:
% 0.37/0.57         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.37/0.57          | (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.37/0.57  thf(fc1_subset_1, axiom,
% 0.37/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.57  thf('8', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.37/0.57  thf('9', plain, (![X0 : $i]: (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.37/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf(t3_xboole_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.57  thf('11', plain, (((sk_B @ (k1_zfmisc_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i]: (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.37/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf(t3_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X11 : $i, X13 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (m1_subset_1 @ (sk_B @ (k1_zfmisc_1 @ X0)) @ (k1_zfmisc_1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.57  thf(t5_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X17 @ X18)
% 0.37/0.57          | ~ (v1_xboole_0 @ X19)
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v1_xboole_0 @ X0)
% 0.37/0.57          | ~ (r2_hidden @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['11', '16'])).
% 0.37/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.57  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.57  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | (v2_struct_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf(t65_tex_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.37/0.57         ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.37/0.57                ( ![C:$i]:
% 0.37/0.57                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.57          | ~ (v2_tex_2 @ X22 @ X23)
% 0.37/0.57          | (v3_tex_2 @ (sk_C_2 @ X22 @ X23) @ X23)
% 0.37/0.57          | ~ (l1_pre_topc @ X23)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X23)
% 0.37/0.57          | ~ (v2_pre_topc @ X23)
% 0.37/0.57          | (v2_struct_0 @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v2_struct_0 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (v3_tex_2 @ (sk_C_2 @ k1_xboole_0 @ X0) @ X0)
% 0.37/0.57          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v2_struct_0 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (v3_tex_2 @ (sk_C_2 @ k1_xboole_0 @ X0) @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | (v2_struct_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v3_tex_2 @ (sk_C_2 @ k1_xboole_0 @ X0) @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | (v2_struct_0 @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | (v2_struct_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '19'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.57          | ~ (v2_tex_2 @ X22 @ X23)
% 0.37/0.57          | (m1_subset_1 @ (sk_C_2 @ X22 @ X23) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.57          | ~ (l1_pre_topc @ X23)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X23)
% 0.37/0.57          | ~ (v2_pre_topc @ X23)
% 0.37/0.57          | (v2_struct_0 @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v2_struct_0 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (m1_subset_1 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.57          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v2_struct_0 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (m1_subset_1 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | (v2_struct_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '29'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (v3_tdlat_3 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | (v2_struct_0 @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X24 : $i]:
% 0.37/0.57         (~ (v3_tex_2 @ X24 @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (v3_tdlat_3 @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (v3_tex_2 @ (sk_C_2 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.57  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('35', plain, ((v3_tdlat_3 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v3_tex_2 @ (sk_C_2 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.37/0.57  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('39', plain, (~ (v3_tex_2 @ (sk_C_2 @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.37/0.57      inference('clc', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (v3_tdlat_3 @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['25', '39'])).
% 0.37/0.57  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('42', plain, ((v3_tdlat_3 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('44', plain, ((v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.37/0.57  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
