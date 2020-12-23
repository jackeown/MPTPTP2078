%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JMYfQ2BlYC

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:42 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 169 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  563 (2348 expanded)
%              Number of equality atoms :   19 (  68 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','12'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_pre_topc @ X20 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('34',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('36',plain,
    ( ( k6_domain_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_C_2 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','45'])).

thf('47',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('49',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('50',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['46','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JMYfQ2BlYC
% 0.15/0.38  % Computer   : n017.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 15:04:02 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 191 iterations in 0.170s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.48/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.66  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.48/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.48/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.48/0.66  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.48/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.66  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.48/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.66  thf(t42_tex_2, conjecture,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.66       ( ![B:$i]:
% 0.48/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.66           ( ( v2_tex_2 @ B @ A ) =>
% 0.48/0.66             ( ![C:$i]:
% 0.48/0.66               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.66                 ( ( r2_hidden @ C @ B ) =>
% 0.48/0.66                   ( ( k9_subset_1 @
% 0.48/0.66                       ( u1_struct_0 @ A ) @ B @ 
% 0.48/0.66                       ( k2_pre_topc @
% 0.48/0.66                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.48/0.66                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i]:
% 0.48/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.66            ( l1_pre_topc @ A ) ) =>
% 0.48/0.66          ( ![B:$i]:
% 0.48/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.66              ( ( v2_tex_2 @ B @ A ) =>
% 0.48/0.66                ( ![C:$i]:
% 0.48/0.66                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.66                    ( ( r2_hidden @ C @ B ) =>
% 0.48/0.66                      ( ( k9_subset_1 @
% 0.48/0.66                          ( u1_struct_0 @ A ) @ B @ 
% 0.48/0.66                          ( k2_pre_topc @
% 0.48/0.66                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.48/0.66                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.48/0.66  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(dt_k6_domain_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.48/0.66       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (![X15 : $i, X16 : $i]:
% 0.48/0.66         ((v1_xboole_0 @ X15)
% 0.48/0.66          | ~ (m1_subset_1 @ X16 @ X15)
% 0.48/0.66          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.48/0.66  thf('3', plain,
% 0.48/0.66      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ 
% 0.48/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.66  thf('4', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(redefinition_k6_domain_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.48/0.66       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.48/0.66  thf('5', plain,
% 0.48/0.66      (![X17 : $i, X18 : $i]:
% 0.48/0.66         ((v1_xboole_0 @ X17)
% 0.48/0.66          | ~ (m1_subset_1 @ X18 @ X17)
% 0.48/0.66          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.48/0.66  thf('6', plain,
% 0.48/0.66      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.48/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(cc1_subset_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_xboole_0 @ A ) =>
% 0.48/0.66       ( ![B:$i]:
% 0.48/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.48/0.66  thf('8', plain,
% 0.48/0.66      (![X11 : $i, X12 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.48/0.66          | (v1_xboole_0 @ X11)
% 0.48/0.66          | ~ (v1_xboole_0 @ X12))),
% 0.48/0.66      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.48/0.66  thf('9', plain,
% 0.48/0.66      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.66  thf('10', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(d1_xboole_0, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.66  thf('12', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.66  thf('13', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('clc', [status(thm)], ['9', '12'])).
% 0.48/0.66  thf('14', plain,
% 0.48/0.66      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.48/0.66      inference('clc', [status(thm)], ['6', '13'])).
% 0.48/0.66  thf('15', plain,
% 0.48/0.66      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.48/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('demod', [status(thm)], ['3', '14'])).
% 0.48/0.66  thf('16', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.48/0.66      inference('clc', [status(thm)], ['9', '12'])).
% 0.48/0.66  thf('17', plain,
% 0.48/0.66      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.48/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('clc', [status(thm)], ['15', '16'])).
% 0.48/0.66  thf('18', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(t41_tex_2, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.66       ( ![B:$i]:
% 0.48/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.66           ( ( v2_tex_2 @ B @ A ) <=>
% 0.48/0.66             ( ![C:$i]:
% 0.48/0.66               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.66                 ( ( r1_tarski @ C @ B ) =>
% 0.48/0.66                   ( ( k9_subset_1 @
% 0.48/0.66                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.48/0.66                     ( C ) ) ) ) ) ) ) ) ))).
% 0.48/0.66  thf('19', plain,
% 0.48/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.48/0.66          | ~ (v2_tex_2 @ X19 @ X20)
% 0.48/0.66          | ~ (r1_tarski @ X21 @ X19)
% 0.48/0.66          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 0.48/0.66              (k2_pre_topc @ X20 @ X21)) = (X21))
% 0.48/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.48/0.66          | ~ (l1_pre_topc @ X20)
% 0.48/0.66          | ~ (v2_pre_topc @ X20)
% 0.48/0.66          | (v2_struct_0 @ X20))),
% 0.48/0.66      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.48/0.66  thf('20', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.48/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.66          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.48/0.66              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.48/0.66          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.48/0.66          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.66  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('23', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('24', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((v2_struct_0 @ sk_A)
% 0.48/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.66          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.48/0.66              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.48/0.66          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.48/0.66  thf('25', plain,
% 0.48/0.66      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.48/0.66        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.48/0.66            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.48/0.66        | (v2_struct_0 @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['17', '24'])).
% 0.48/0.66  thf(d3_tarski, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.66  thf('26', plain,
% 0.48/0.66      (![X4 : $i, X6 : $i]:
% 0.48/0.66         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.48/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.66  thf('27', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(t1_subset, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.48/0.66  thf('28', plain,
% 0.48/0.66      (![X13 : $i, X14 : $i]:
% 0.48/0.66         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.48/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.48/0.66  thf('29', plain, ((m1_subset_1 @ sk_C_2 @ sk_B_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.66  thf('30', plain,
% 0.48/0.66      (![X15 : $i, X16 : $i]:
% 0.48/0.66         ((v1_xboole_0 @ X15)
% 0.48/0.66          | ~ (m1_subset_1 @ X16 @ X15)
% 0.48/0.66          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.48/0.66  thf('31', plain,
% 0.48/0.66      (((m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))
% 0.48/0.66        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.66  thf('32', plain, ((m1_subset_1 @ sk_C_2 @ sk_B_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.66  thf('33', plain,
% 0.48/0.66      (![X17 : $i, X18 : $i]:
% 0.48/0.66         ((v1_xboole_0 @ X17)
% 0.48/0.66          | ~ (m1_subset_1 @ X18 @ X17)
% 0.48/0.66          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.48/0.66  thf('34', plain,
% 0.48/0.66      ((((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.48/0.66        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.48/0.66  thf('35', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.66  thf('36', plain, (((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.48/0.66      inference('clc', [status(thm)], ['34', '35'])).
% 0.48/0.66  thf('37', plain,
% 0.48/0.66      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))
% 0.48/0.66        | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['31', '36'])).
% 0.48/0.66  thf('38', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.66  thf('39', plain,
% 0.48/0.66      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.48/0.66      inference('clc', [status(thm)], ['37', '38'])).
% 0.48/0.66  thf(l3_subset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.48/0.66  thf('40', plain,
% 0.48/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X8 @ X9)
% 0.48/0.66          | (r2_hidden @ X8 @ X10)
% 0.48/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.48/0.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.48/0.66  thf('41', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_2)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['39', '40'])).
% 0.48/0.66  thf('42', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((r1_tarski @ (k1_tarski @ sk_C_2) @ X0)
% 0.48/0.66          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_C_2)) @ sk_B_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['26', '41'])).
% 0.48/0.66  thf('43', plain,
% 0.48/0.66      (![X4 : $i, X6 : $i]:
% 0.48/0.66         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.48/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.66  thf('44', plain,
% 0.48/0.66      (((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.48/0.66        | (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.48/0.66  thf('45', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.48/0.66      inference('simplify', [status(thm)], ['44'])).
% 0.48/0.66  thf('46', plain,
% 0.48/0.66      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.48/0.66          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.48/0.66        | (v2_struct_0 @ sk_A))),
% 0.48/0.66      inference('demod', [status(thm)], ['25', '45'])).
% 0.48/0.66  thf('47', plain,
% 0.48/0.66      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.48/0.66         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.48/0.66         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('48', plain,
% 0.48/0.66      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.48/0.66      inference('clc', [status(thm)], ['6', '13'])).
% 0.48/0.66  thf('49', plain,
% 0.48/0.66      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.48/0.66      inference('clc', [status(thm)], ['6', '13'])).
% 0.48/0.66  thf('50', plain,
% 0.48/0.66      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.48/0.66         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.48/0.66      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.48/0.66  thf('51', plain, ((v2_struct_0 @ sk_A)),
% 0.48/0.66      inference('simplify_reflect-', [status(thm)], ['46', '50'])).
% 0.48/0.66  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
