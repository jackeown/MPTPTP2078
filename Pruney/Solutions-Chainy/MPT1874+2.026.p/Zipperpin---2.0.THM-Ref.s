%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7wJlDfbNWV

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:44 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 130 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  581 (1795 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t42_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('14',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_pre_topc @ X21 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( m1_subset_1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k6_domain_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k6_domain_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('45',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_C_2 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','47'])).

thf('49',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['6','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7wJlDfbNWV
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.71  % Solved by: fo/fo7.sh
% 0.51/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.71  % done 344 iterations in 0.217s
% 0.51/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.71  % SZS output start Refutation
% 0.51/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.71  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.51/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.71  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.51/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.51/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.71  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.51/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.71  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.51/0.71  thf(t42_tex_2, conjecture,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.71       ( ![B:$i]:
% 0.51/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.71           ( ( v2_tex_2 @ B @ A ) =>
% 0.51/0.71             ( ![C:$i]:
% 0.51/0.71               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.71                 ( ( r2_hidden @ C @ B ) =>
% 0.51/0.71                   ( ( k9_subset_1 @
% 0.51/0.71                       ( u1_struct_0 @ A ) @ B @ 
% 0.51/0.71                       ( k2_pre_topc @
% 0.51/0.71                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.51/0.71                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.71    (~( ![A:$i]:
% 0.51/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.71            ( l1_pre_topc @ A ) ) =>
% 0.51/0.71          ( ![B:$i]:
% 0.51/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.71              ( ( v2_tex_2 @ B @ A ) =>
% 0.51/0.71                ( ![C:$i]:
% 0.51/0.71                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.71                    ( ( r2_hidden @ C @ B ) =>
% 0.51/0.71                      ( ( k9_subset_1 @
% 0.51/0.71                          ( u1_struct_0 @ A ) @ B @ 
% 0.51/0.71                          ( k2_pre_topc @
% 0.51/0.71                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.51/0.71                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.51/0.71    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.51/0.71  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('1', plain,
% 0.51/0.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(l3_subset_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.51/0.71  thf('2', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X10 @ X11)
% 0.51/0.71          | (r2_hidden @ X10 @ X12)
% 0.51/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.51/0.71      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.51/0.71  thf('3', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.71  thf('4', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['0', '3'])).
% 0.51/0.71  thf(d1_xboole_0, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.71  thf('5', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.71  thf('6', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.71  thf('7', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(redefinition_k6_domain_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.51/0.71       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.51/0.71  thf('8', plain,
% 0.51/0.71      (![X18 : $i, X19 : $i]:
% 0.51/0.71         ((v1_xboole_0 @ X18)
% 0.51/0.71          | ~ (m1_subset_1 @ X19 @ X18)
% 0.51/0.71          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.51/0.71      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.51/0.71  thf('9', plain,
% 0.51/0.71      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.51/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.71  thf('10', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(dt_k6_domain_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.51/0.71       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.71  thf('11', plain,
% 0.51/0.71      (![X16 : $i, X17 : $i]:
% 0.51/0.71         ((v1_xboole_0 @ X16)
% 0.51/0.71          | ~ (m1_subset_1 @ X17 @ X16)
% 0.51/0.71          | (m1_subset_1 @ (k6_domain_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16)))),
% 0.51/0.71      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.51/0.71  thf('12', plain,
% 0.51/0.71      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ 
% 0.51/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.71  thf('13', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.71  thf('14', plain,
% 0.51/0.71      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ 
% 0.51/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.71      inference('clc', [status(thm)], ['12', '13'])).
% 0.51/0.71  thf('15', plain,
% 0.51/0.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(t41_tex_2, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.71       ( ![B:$i]:
% 0.51/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.71           ( ( v2_tex_2 @ B @ A ) <=>
% 0.51/0.71             ( ![C:$i]:
% 0.51/0.71               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.71                 ( ( r1_tarski @ C @ B ) =>
% 0.51/0.71                   ( ( k9_subset_1 @
% 0.51/0.71                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.51/0.71                     ( C ) ) ) ) ) ) ) ) ))).
% 0.51/0.71  thf('16', plain,
% 0.51/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.51/0.71          | ~ (v2_tex_2 @ X20 @ X21)
% 0.51/0.71          | ~ (r1_tarski @ X22 @ X20)
% 0.51/0.71          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 0.51/0.71              (k2_pre_topc @ X21 @ X22)) = (X22))
% 0.51/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.51/0.71          | ~ (l1_pre_topc @ X21)
% 0.51/0.71          | ~ (v2_pre_topc @ X21)
% 0.51/0.71          | (v2_struct_0 @ X21))),
% 0.51/0.71      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.51/0.71  thf('17', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((v2_struct_0 @ sk_A)
% 0.51/0.71          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.71          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.51/0.71              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.51/0.71          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.51/0.71          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.51/0.71  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('20', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('21', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((v2_struct_0 @ sk_A)
% 0.51/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.71          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.51/0.71              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.51/0.71          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.51/0.71      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.51/0.71  thf('22', plain,
% 0.51/0.71      ((~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ sk_B_1)
% 0.51/0.71        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.51/0.71            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.51/0.71            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 0.51/0.71        | (v2_struct_0 @ sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['14', '21'])).
% 0.51/0.71  thf('23', plain,
% 0.51/0.71      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.51/0.71         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.51/0.71         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('24', plain,
% 0.51/0.71      ((~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ sk_B_1)
% 0.51/0.71        | (v2_struct_0 @ sk_A))),
% 0.51/0.71      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.51/0.71  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('26', plain,
% 0.51/0.71      (~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ sk_B_1)),
% 0.51/0.71      inference('clc', [status(thm)], ['24', '25'])).
% 0.51/0.71  thf('27', plain,
% 0.51/0.71      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.51/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['9', '26'])).
% 0.51/0.71  thf(d3_tarski, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.71  thf('28', plain,
% 0.51/0.71      (![X4 : $i, X6 : $i]:
% 0.51/0.71         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.51/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.71  thf('29', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(d2_subset_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( v1_xboole_0 @ A ) =>
% 0.51/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.51/0.71       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.71  thf('30', plain,
% 0.51/0.71      (![X7 : $i, X8 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X7 @ X8)
% 0.51/0.71          | (m1_subset_1 @ X7 @ X8)
% 0.51/0.71          | (v1_xboole_0 @ X8))),
% 0.51/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.51/0.71  thf('31', plain,
% 0.51/0.71      (((v1_xboole_0 @ sk_B_1) | (m1_subset_1 @ sk_C_2 @ sk_B_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.51/0.71  thf('32', plain,
% 0.51/0.71      (![X16 : $i, X17 : $i]:
% 0.51/0.71         ((v1_xboole_0 @ X16)
% 0.51/0.71          | ~ (m1_subset_1 @ X17 @ X16)
% 0.51/0.71          | (m1_subset_1 @ (k6_domain_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16)))),
% 0.51/0.71      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.51/0.71  thf('33', plain,
% 0.51/0.71      (((v1_xboole_0 @ sk_B_1)
% 0.51/0.71        | (m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_2) @ 
% 0.51/0.71           (k1_zfmisc_1 @ sk_B_1))
% 0.51/0.71        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.51/0.71  thf('34', plain,
% 0.51/0.71      (((v1_xboole_0 @ sk_B_1) | (m1_subset_1 @ sk_C_2 @ sk_B_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.51/0.71  thf('35', plain,
% 0.51/0.71      (![X18 : $i, X19 : $i]:
% 0.51/0.71         ((v1_xboole_0 @ X18)
% 0.51/0.71          | ~ (m1_subset_1 @ X19 @ X18)
% 0.51/0.71          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.51/0.71      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.51/0.71  thf('36', plain,
% 0.51/0.71      (((v1_xboole_0 @ sk_B_1)
% 0.51/0.71        | ((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.51/0.71        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.71  thf('37', plain,
% 0.51/0.71      ((((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.51/0.71        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.71      inference('simplify', [status(thm)], ['36'])).
% 0.51/0.71  thf('38', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('39', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.71  thf('40', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.51/0.71  thf('41', plain, (((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.51/0.71      inference('clc', [status(thm)], ['37', '40'])).
% 0.51/0.71  thf('42', plain,
% 0.51/0.71      (((v1_xboole_0 @ sk_B_1)
% 0.51/0.71        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))
% 0.51/0.71        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.71      inference('demod', [status(thm)], ['33', '41'])).
% 0.51/0.71  thf('43', plain,
% 0.51/0.71      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))
% 0.51/0.71        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.71      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.71  thf('44', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.51/0.71  thf('45', plain,
% 0.51/0.71      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.51/0.71      inference('clc', [status(thm)], ['43', '44'])).
% 0.51/0.71  thf('46', plain,
% 0.51/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X10 @ X11)
% 0.51/0.71          | (r2_hidden @ X10 @ X12)
% 0.51/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.51/0.71      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.51/0.71  thf('47', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_2)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.51/0.71  thf('48', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((r1_tarski @ (k1_tarski @ sk_C_2) @ X0)
% 0.51/0.71          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_C_2)) @ sk_B_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['28', '47'])).
% 0.51/0.71  thf('49', plain,
% 0.51/0.71      (![X4 : $i, X6 : $i]:
% 0.51/0.71         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.51/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.71  thf('50', plain,
% 0.51/0.71      (((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.51/0.71        | (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.51/0.71  thf('51', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.51/0.71      inference('simplify', [status(thm)], ['50'])).
% 0.51/0.71  thf('52', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.51/0.71      inference('demod', [status(thm)], ['27', '51'])).
% 0.51/0.71  thf('53', plain, ($false), inference('demod', [status(thm)], ['6', '52'])).
% 0.51/0.71  
% 0.51/0.71  % SZS output end Refutation
% 0.51/0.71  
% 0.51/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
