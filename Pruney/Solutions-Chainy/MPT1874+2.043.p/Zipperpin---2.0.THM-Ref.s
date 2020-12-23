%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C25JaifaPy

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 (  84 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  462 (1280 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ ( k2_pre_topc @ X14 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('25',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('31',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','31'])).

thf('33',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C25JaifaPy
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:37:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 76 iterations in 0.034s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.19/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.19/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(t42_tex_2, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v2_tex_2 @ B @ A ) =>
% 0.19/0.53             ( ![C:$i]:
% 0.19/0.53               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                 ( ( r2_hidden @ C @ B ) =>
% 0.19/0.53                   ( ( k9_subset_1 @
% 0.19/0.53                       ( u1_struct_0 @ A ) @ B @ 
% 0.19/0.53                       ( k2_pre_topc @
% 0.19/0.53                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.19/0.53                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.53            ( l1_pre_topc @ A ) ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53              ( ( v2_tex_2 @ B @ A ) =>
% 0.19/0.53                ( ![C:$i]:
% 0.19/0.53                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                    ( ( r2_hidden @ C @ B ) =>
% 0.19/0.53                      ( ( k9_subset_1 @
% 0.19/0.53                          ( u1_struct_0 @ A ) @ B @ 
% 0.19/0.53                          ( k2_pre_topc @
% 0.19/0.53                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.19/0.53                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.19/0.53  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t5_subset, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X8 @ X9)
% 0.19/0.53          | ~ (v1_xboole_0 @ X10)
% 0.19/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d2_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X3 @ X4)
% 0.19/0.53          | (r2_hidden @ X3 @ X4)
% 0.19/0.53          | (v1_xboole_0 @ X4))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.53  thf(t63_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.19/0.53       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.19/0.53          | ~ (r2_hidden @ X6 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.19/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t41_tex_2, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v2_tex_2 @ B @ A ) <=>
% 0.19/0.53             ( ![C:$i]:
% 0.19/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53                 ( ( r1_tarski @ C @ B ) =>
% 0.19/0.53                   ( ( k9_subset_1 @
% 0.19/0.53                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.19/0.53                     ( C ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.19/0.53          | ~ (v2_tex_2 @ X13 @ X14)
% 0.19/0.53          | ~ (r1_tarski @ X15 @ X13)
% 0.19/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X14) @ X13 @ 
% 0.19/0.53              (k2_pre_topc @ X14 @ X15)) = (X15))
% 0.19/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.19/0.53          | ~ (l1_pre_topc @ X14)
% 0.19/0.53          | ~ (v2_pre_topc @ X14)
% 0.19/0.53          | (v2_struct_0 @ X14))),
% 0.19/0.53      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ sk_A)
% 0.19/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.53          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.53              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.19/0.53          | ~ (r1_tarski @ X0 @ sk_B)
% 0.19/0.53          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.53  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('14', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ sk_A)
% 0.19/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.53          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.53              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.19/0.53          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.19/0.53        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.53            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.19/0.53        | (v2_struct_0 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['8', '15'])).
% 0.19/0.53  thf('17', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(l1_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X0 : $i, X2 : $i]:
% 0.19/0.53         ((r1_tarski @ (k1_tarski @ X0) @ X2) | ~ (r2_hidden @ X0 @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.53  thf('19', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.19/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.53            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.19/0.53        | (v2_struct_0 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['16', '19'])).
% 0.19/0.53  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.53          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('clc', [status(thm)], ['20', '21'])).
% 0.19/0.53  thf('23', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X11 : $i, X12 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X11)
% 0.19/0.53          | ~ (m1_subset_1 @ X12 @ X11)
% 0.19/0.53          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.53         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.19/0.53         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.53          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.19/0.53          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      ((((k1_tarski @ sk_C_1) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['22', '27'])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | ((k1_tarski @ sk_C_1)
% 0.19/0.53            != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.53  thf('31', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('clc', [status(thm)], ['29', '30'])).
% 0.19/0.53  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.19/0.53      inference('demod', [status(thm)], ['3', '31'])).
% 0.19/0.53  thf('33', plain, ($false), inference('sup-', [status(thm)], ['0', '32'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
