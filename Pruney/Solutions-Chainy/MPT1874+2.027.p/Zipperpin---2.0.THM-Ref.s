%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BJgwlVc6dP

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:45 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 179 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  554 (2433 expanded)
%              Number of equality atoms :   19 (  68 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( ( k6_domain_1 @ X43 @ X44 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v2_tex_2 @ X45 @ X46 )
      | ~ ( r1_tarski @ X47 @ X45 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_pre_topc @ X46 @ X47 ) )
        = X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( m1_subset_1 @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X35: $i,X36: $i] :
      ( ( m1_subset_1 @ X35 @ X36 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('36',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( ( k6_domain_1 @ X43 @ X44 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('37',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

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
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('44',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','46'])).

thf('48',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('50',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('51',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['47','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BJgwlVc6dP
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:23 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 411 iterations in 0.397s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.87  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.68/0.87  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.68/0.87  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.87  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.68/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.87  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.68/0.87  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.68/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(t42_tex_2, conjecture,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.87           ( ( v2_tex_2 @ B @ A ) =>
% 0.68/0.87             ( ![C:$i]:
% 0.68/0.87               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87                 ( ( r2_hidden @ C @ B ) =>
% 0.68/0.87                   ( ( k9_subset_1 @
% 0.68/0.87                       ( u1_struct_0 @ A ) @ B @ 
% 0.68/0.87                       ( k2_pre_topc @
% 0.68/0.87                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.68/0.87                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i]:
% 0.68/0.87        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.68/0.87            ( l1_pre_topc @ A ) ) =>
% 0.68/0.87          ( ![B:$i]:
% 0.68/0.87            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.87              ( ( v2_tex_2 @ B @ A ) =>
% 0.68/0.87                ( ![C:$i]:
% 0.68/0.87                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87                    ( ( r2_hidden @ C @ B ) =>
% 0.68/0.87                      ( ( k9_subset_1 @
% 0.68/0.87                          ( u1_struct_0 @ A ) @ B @ 
% 0.68/0.87                          ( k2_pre_topc @
% 0.68/0.87                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.68/0.87                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.68/0.87  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(dt_k6_domain_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.68/0.87       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (![X41 : $i, X42 : $i]:
% 0.68/0.87         ((v1_xboole_0 @ X41)
% 0.68/0.87          | ~ (m1_subset_1 @ X42 @ X41)
% 0.68/0.87          | (m1_subset_1 @ (k6_domain_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41)))),
% 0.68/0.87      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.68/0.87  thf('3', plain,
% 0.68/0.87      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ 
% 0.68/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.87  thf('4', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(redefinition_k6_domain_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.68/0.87       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      (![X43 : $i, X44 : $i]:
% 0.68/0.87         ((v1_xboole_0 @ X43)
% 0.68/0.87          | ~ (m1_subset_1 @ X44 @ X43)
% 0.68/0.87          | ((k6_domain_1 @ X43 @ X44) = (k1_tarski @ X44)))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.87  thf('7', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(t3_subset, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.87  thf('9', plain,
% 0.68/0.87      (![X38 : $i, X39 : $i]:
% 0.68/0.87         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.87  thf('10', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.87  thf(d3_tarski, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.87  thf('11', plain,
% 0.68/0.87      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X3 @ X4)
% 0.68/0.87          | (r2_hidden @ X3 @ X5)
% 0.68/0.87          | ~ (r1_tarski @ X4 @ X5))),
% 0.68/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.87  thf('12', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.87  thf('13', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['7', '12'])).
% 0.68/0.87  thf(d1_xboole_0, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.68/0.87  thf('14', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.87  thf('15', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['13', '14'])).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.68/0.87      inference('clc', [status(thm)], ['6', '15'])).
% 0.68/0.87  thf('17', plain,
% 0.68/0.87      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.68/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('demod', [status(thm)], ['3', '16'])).
% 0.68/0.87  thf('18', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['13', '14'])).
% 0.68/0.87  thf('19', plain,
% 0.68/0.87      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.68/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('clc', [status(thm)], ['17', '18'])).
% 0.68/0.87  thf('20', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(t41_tex_2, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.87           ( ( v2_tex_2 @ B @ A ) <=>
% 0.68/0.87             ( ![C:$i]:
% 0.68/0.87               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.87                 ( ( r1_tarski @ C @ B ) =>
% 0.68/0.87                   ( ( k9_subset_1 @
% 0.68/0.87                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.68/0.87                     ( C ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf('21', plain,
% 0.68/0.87      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.68/0.87          | ~ (v2_tex_2 @ X45 @ X46)
% 0.68/0.87          | ~ (r1_tarski @ X47 @ X45)
% 0.68/0.87          | ((k9_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 0.68/0.87              (k2_pre_topc @ X46 @ X47)) = (X47))
% 0.68/0.87          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.68/0.87          | ~ (l1_pre_topc @ X46)
% 0.68/0.87          | ~ (v2_pre_topc @ X46)
% 0.68/0.87          | (v2_struct_0 @ X46))),
% 0.68/0.87      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.68/0.87  thf('22', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (v2_pre_topc @ sk_A)
% 0.68/0.87          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.68/0.87              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.68/0.87          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.68/0.87          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.87  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('25', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('26', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.68/0.87              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.68/0.87          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.68/0.87  thf('27', plain,
% 0.68/0.87      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.68/0.87        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.68/0.87            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['19', '26'])).
% 0.68/0.87  thf('28', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(d2_subset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( v1_xboole_0 @ A ) =>
% 0.68/0.87         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.68/0.87       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.68/0.87         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.68/0.87  thf('29', plain,
% 0.68/0.87      (![X35 : $i, X36 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X35 @ X36)
% 0.68/0.87          | (m1_subset_1 @ X35 @ X36)
% 0.68/0.87          | (v1_xboole_0 @ X36))),
% 0.68/0.87      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.68/0.87  thf('30', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.87  thf('31', plain,
% 0.68/0.87      (![X35 : $i, X36 : $i]:
% 0.68/0.87         ((m1_subset_1 @ X35 @ X36) | ~ (r2_hidden @ X35 @ X36))),
% 0.68/0.87      inference('clc', [status(thm)], ['29', '30'])).
% 0.68/0.87  thf('32', plain, ((m1_subset_1 @ sk_C_2 @ sk_B_1)),
% 0.68/0.87      inference('sup-', [status(thm)], ['28', '31'])).
% 0.68/0.87  thf('33', plain,
% 0.68/0.87      (![X41 : $i, X42 : $i]:
% 0.68/0.87         ((v1_xboole_0 @ X41)
% 0.68/0.87          | ~ (m1_subset_1 @ X42 @ X41)
% 0.68/0.87          | (m1_subset_1 @ (k6_domain_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41)))),
% 0.68/0.87      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.68/0.87  thf('34', plain,
% 0.68/0.87      (((m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))
% 0.68/0.87        | (v1_xboole_0 @ sk_B_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['32', '33'])).
% 0.68/0.87  thf('35', plain, ((m1_subset_1 @ sk_C_2 @ sk_B_1)),
% 0.68/0.87      inference('sup-', [status(thm)], ['28', '31'])).
% 0.68/0.87  thf('36', plain,
% 0.68/0.87      (![X43 : $i, X44 : $i]:
% 0.68/0.87         ((v1_xboole_0 @ X43)
% 0.68/0.87          | ~ (m1_subset_1 @ X44 @ X43)
% 0.68/0.87          | ((k6_domain_1 @ X43 @ X44) = (k1_tarski @ X44)))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.68/0.87  thf('37', plain,
% 0.68/0.87      ((((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.68/0.87        | (v1_xboole_0 @ sk_B_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['35', '36'])).
% 0.68/0.87  thf('38', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('39', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.87  thf('40', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.68/0.87      inference('sup-', [status(thm)], ['38', '39'])).
% 0.68/0.87  thf('41', plain, (((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.68/0.87      inference('clc', [status(thm)], ['37', '40'])).
% 0.68/0.87  thf('42', plain,
% 0.68/0.87      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))
% 0.68/0.87        | (v1_xboole_0 @ sk_B_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['34', '41'])).
% 0.68/0.87  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.68/0.87      inference('sup-', [status(thm)], ['38', '39'])).
% 0.68/0.87  thf('44', plain,
% 0.68/0.87      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.68/0.87      inference('clc', [status(thm)], ['42', '43'])).
% 0.68/0.87  thf('45', plain,
% 0.68/0.87      (![X38 : $i, X39 : $i]:
% 0.68/0.87         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.87  thf('46', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.68/0.87      inference('sup-', [status(thm)], ['44', '45'])).
% 0.68/0.87  thf('47', plain,
% 0.68/0.87      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.68/0.87          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['27', '46'])).
% 0.68/0.87  thf('48', plain,
% 0.68/0.87      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.68/0.87         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.68/0.87         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('49', plain,
% 0.68/0.87      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.68/0.87      inference('clc', [status(thm)], ['6', '15'])).
% 0.68/0.87  thf('50', plain,
% 0.68/0.87      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.68/0.87      inference('clc', [status(thm)], ['6', '15'])).
% 0.68/0.87  thf('51', plain,
% 0.68/0.87      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.68/0.87         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.68/0.87      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.68/0.87  thf('52', plain, ((v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('simplify_reflect-', [status(thm)], ['47', '51'])).
% 0.68/0.87  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.68/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
