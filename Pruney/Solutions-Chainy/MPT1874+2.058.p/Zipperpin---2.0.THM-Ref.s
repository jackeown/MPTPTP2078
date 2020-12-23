%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OqqqRWDvCH

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:49 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   60 (  82 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  439 (1231 expanded)
%              Number of equality atoms :   13 (  35 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ X37 )
      | ( ( k6_domain_1 @ X37 @ X38 )
        = ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ X35 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v2_tex_2 @ X39 @ X40 )
      | ~ ( r1_tarski @ X41 @ X39 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 @ ( k2_pre_topc @ X40 @ X41 ) )
        = X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','31'])).

thf('33',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OqqqRWDvCH
% 0.14/0.37  % Computer   : n019.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:27:22 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 59 iterations in 0.022s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.24/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.24/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.50  thf(t42_tex_2, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.50           ( ( v2_tex_2 @ B @ A ) =>
% 0.24/0.50             ( ![C:$i]:
% 0.24/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.50                 ( ( r2_hidden @ C @ B ) =>
% 0.24/0.50                   ( ( k9_subset_1 @
% 0.24/0.50                       ( u1_struct_0 @ A ) @ B @ 
% 0.24/0.50                       ( k2_pre_topc @
% 0.24/0.50                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.24/0.50                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.50            ( l1_pre_topc @ A ) ) =>
% 0.24/0.50          ( ![B:$i]:
% 0.24/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.50              ( ( v2_tex_2 @ B @ A ) =>
% 0.24/0.50                ( ![C:$i]:
% 0.24/0.50                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.50                    ( ( r2_hidden @ C @ B ) =>
% 0.24/0.50                      ( ( k9_subset_1 @
% 0.24/0.50                          ( u1_struct_0 @ A ) @ B @ 
% 0.24/0.50                          ( k2_pre_topc @
% 0.24/0.50                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.24/0.50                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.24/0.50  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t5_subset, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.24/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X32 @ X33)
% 0.24/0.50          | ~ (v1_xboole_0 @ X34)
% 0.24/0.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.24/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.24/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.50  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X37 : $i, X38 : $i]:
% 0.24/0.50         ((v1_xboole_0 @ X37)
% 0.24/0.50          | ~ (m1_subset_1 @ X38 @ X37)
% 0.24/0.50          | ((k6_domain_1 @ X37 @ X38) = (k1_tarski @ X38)))),
% 0.24/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.24/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.50  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(dt_k6_domain_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.50       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X35 : $i, X36 : $i]:
% 0.24/0.50         ((v1_xboole_0 @ X35)
% 0.24/0.50          | ~ (m1_subset_1 @ X36 @ X35)
% 0.24/0.50          | (m1_subset_1 @ (k6_domain_1 @ X35 @ X36) @ (k1_zfmisc_1 @ X35)))),
% 0.24/0.50      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.24/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t41_tex_2, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.50           ( ( v2_tex_2 @ B @ A ) <=>
% 0.24/0.50             ( ![C:$i]:
% 0.24/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.50                 ( ( r1_tarski @ C @ B ) =>
% 0.24/0.50                   ( ( k9_subset_1 @
% 0.24/0.50                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.24/0.50                     ( C ) ) ) ) ) ) ) ) ))).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.24/0.50         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.24/0.50          | ~ (v2_tex_2 @ X39 @ X40)
% 0.24/0.50          | ~ (r1_tarski @ X41 @ X39)
% 0.24/0.50          | ((k9_subset_1 @ (u1_struct_0 @ X40) @ X39 @ 
% 0.24/0.50              (k2_pre_topc @ X40 @ X41)) = (X41))
% 0.24/0.50          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.24/0.50          | ~ (l1_pre_topc @ X40)
% 0.24/0.50          | ~ (v2_pre_topc @ X40)
% 0.24/0.50          | (v2_struct_0 @ X40))),
% 0.24/0.50      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((v2_struct_0 @ sk_A)
% 0.24/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.50          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.50              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.24/0.50          | ~ (r1_tarski @ X0 @ sk_B)
% 0.24/0.50          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.50  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('15', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('16', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((v2_struct_0 @ sk_A)
% 0.24/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.50          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.50              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.24/0.50          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.24/0.50      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.50        | ~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.24/0.50        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.50            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.24/0.50            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.24/0.50        | (v2_struct_0 @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['9', '16'])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.50         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.24/0.50         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('19', plain,
% 0.24/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.50        | ~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.24/0.50        | (v2_struct_0 @ sk_A))),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.24/0.50  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('21', plain,
% 0.24/0.50      ((~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.24/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.50      inference('clc', [status(thm)], ['19', '20'])).
% 0.24/0.50  thf('22', plain,
% 0.24/0.50      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.24/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['6', '21'])).
% 0.24/0.50  thf('23', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('24', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t38_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.24/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.24/0.50  thf('25', plain,
% 0.24/0.50      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.24/0.50         ((r1_tarski @ (k2_tarski @ X28 @ X30) @ X31)
% 0.24/0.50          | ~ (r2_hidden @ X30 @ X31)
% 0.24/0.50          | ~ (r2_hidden @ X28 @ X31))),
% 0.24/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.24/0.50  thf('26', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.24/0.50          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B))),
% 0.24/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.50  thf('27', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_B)),
% 0.24/0.50      inference('sup-', [status(thm)], ['23', '26'])).
% 0.24/0.50  thf(t69_enumset1, axiom,
% 0.24/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.50  thf('28', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.50  thf('29', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.24/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.24/0.50  thf('30', plain,
% 0.24/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.50      inference('demod', [status(thm)], ['22', '29'])).
% 0.24/0.50  thf('31', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.24/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.24/0.50  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.24/0.50      inference('demod', [status(thm)], ['3', '31'])).
% 0.24/0.50  thf('33', plain, ($false), inference('sup-', [status(thm)], ['0', '32'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
