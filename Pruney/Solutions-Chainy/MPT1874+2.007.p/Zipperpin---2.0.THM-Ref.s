%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oJ0lzLBVuC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:42 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 124 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  473 (1765 expanded)
%              Number of equality atoms :   17 (  54 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X11 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_2 @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_pre_topc @ X23 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('25',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('29',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('38',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('39',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['26','37','38'])).

thf('40',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['25','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oJ0lzLBVuC
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 354 iterations in 0.141s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.42/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.42/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.59  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.59  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.42/0.59  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.42/0.59  thf(t42_tex_2, conjecture,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( v2_tex_2 @ B @ A ) =>
% 0.42/0.59             ( ![C:$i]:
% 0.42/0.59               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59                 ( ( r2_hidden @ C @ B ) =>
% 0.42/0.59                   ( ( k9_subset_1 @
% 0.42/0.59                       ( u1_struct_0 @ A ) @ B @ 
% 0.42/0.59                       ( k2_pre_topc @
% 0.42/0.59                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.42/0.59                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i]:
% 0.42/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.59            ( l1_pre_topc @ A ) ) =>
% 0.42/0.59          ( ![B:$i]:
% 0.42/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59              ( ( v2_tex_2 @ B @ A ) =>
% 0.42/0.59                ( ![C:$i]:
% 0.42/0.59                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59                    ( ( r2_hidden @ C @ B ) =>
% 0.42/0.59                      ( ( k9_subset_1 @
% 0.42/0.59                          ( u1_struct_0 @ A ) @ B @ 
% 0.42/0.59                          ( k2_pre_topc @
% 0.42/0.59                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.42/0.59                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.42/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t3_subset, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      (![X17 : $i, X18 : $i]:
% 0.42/0.59         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('3', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.59  thf('4', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('5', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t38_zfmisc_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.42/0.59       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.42/0.59  thf('6', plain,
% 0.42/0.59      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.42/0.59         ((r1_tarski @ (k2_tarski @ X11 @ X13) @ X14)
% 0.42/0.59          | ~ (r2_hidden @ X13 @ X14)
% 0.42/0.59          | ~ (r2_hidden @ X11 @ X14))),
% 0.42/0.59      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.42/0.59  thf('7', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.42/0.59          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ sk_B_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.59  thf('8', plain, ((r1_tarski @ (k2_tarski @ sk_C_2 @ sk_C_2) @ sk_B_1)),
% 0.42/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.42/0.59  thf(t69_enumset1, axiom,
% 0.42/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.59  thf('9', plain, (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.42/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.59  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.42/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf(t1_xboole_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.42/0.59       ( r1_tarski @ A @ C ) ))).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.59         (~ (r1_tarski @ X7 @ X8)
% 0.42/0.59          | ~ (r1_tarski @ X8 @ X9)
% 0.42/0.59          | (r1_tarski @ X7 @ X9))),
% 0.42/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r1_tarski @ (k1_tarski @ sk_C_2) @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.59  thf('13', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['3', '12'])).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      (![X17 : $i, X19 : $i]:
% 0.42/0.59         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('15', plain,
% 0.42/0.59      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.42/0.59  thf('16', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t41_tex_2, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( v2_tex_2 @ B @ A ) <=>
% 0.42/0.59             ( ![C:$i]:
% 0.42/0.59               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59                 ( ( r1_tarski @ C @ B ) =>
% 0.42/0.59                   ( ( k9_subset_1 @
% 0.42/0.59                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.42/0.59                     ( C ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.59          | ~ (v2_tex_2 @ X22 @ X23)
% 0.42/0.59          | ~ (r1_tarski @ X24 @ X22)
% 0.42/0.59          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.42/0.59              (k2_pre_topc @ X23 @ X24)) = (X24))
% 0.42/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.59          | ~ (l1_pre_topc @ X23)
% 0.42/0.59          | ~ (v2_pre_topc @ X23)
% 0.42/0.59          | (v2_struct_0 @ X23))),
% 0.42/0.59      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.42/0.59  thf('18', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.42/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.42/0.59              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.42/0.59          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.42/0.59          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('21', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.42/0.59              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.42/0.59          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.42/0.59      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.42/0.59  thf('23', plain,
% 0.42/0.59      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.42/0.59        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.42/0.59            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.42/0.59        | (v2_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['15', '22'])).
% 0.42/0.59  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.42/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf('25', plain,
% 0.42/0.59      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.42/0.59          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.42/0.59        | (v2_struct_0 @ sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.42/0.59         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.42/0.59         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('27', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(redefinition_k6_domain_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.42/0.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.42/0.59  thf('28', plain,
% 0.42/0.59      (![X20 : $i, X21 : $i]:
% 0.42/0.59         ((v1_xboole_0 @ X20)
% 0.42/0.59          | ~ (m1_subset_1 @ X21 @ X20)
% 0.42/0.59          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.42/0.59  thf('29', plain,
% 0.42/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.42/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(cc1_subset_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      (![X15 : $i, X16 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.42/0.59          | (v1_xboole_0 @ X15)
% 0.42/0.59          | ~ (v1_xboole_0 @ X16))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.59  thf('33', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(d1_xboole_0, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.59  thf('34', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.59  thf('35', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.42/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.59  thf('36', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('clc', [status(thm)], ['32', '35'])).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.42/0.59      inference('clc', [status(thm)], ['29', '36'])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.42/0.59      inference('clc', [status(thm)], ['29', '36'])).
% 0.42/0.59  thf('39', plain,
% 0.42/0.59      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.42/0.59         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.42/0.59      inference('demod', [status(thm)], ['26', '37', '38'])).
% 0.42/0.59  thf('40', plain, ((v2_struct_0 @ sk_A)),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['25', '39'])).
% 0.42/0.59  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
