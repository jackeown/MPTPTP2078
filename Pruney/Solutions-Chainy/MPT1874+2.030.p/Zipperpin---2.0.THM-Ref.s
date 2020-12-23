%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4oHAPp930O

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:45 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 223 expanded)
%              Number of leaves         :   28 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  574 (2713 expanded)
%              Number of equality atoms :   16 (  69 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( m1_subset_1 @ X38 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

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
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','6'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ X44 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','6'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X46: $i,X47: $i] :
      ( ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ X46 )
      | ( ( k6_domain_1 @ X46 @ X47 )
        = ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X46: $i,X47: $i] :
      ( ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ X46 )
      | ( ( k6_domain_1 @ X46 @ X47 )
        = ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('33',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ X44 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('38',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v2_tex_2 @ X48 @ X49 )
      | ~ ( r1_tarski @ X50 @ X48 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_pre_topc @ X49 @ X50 ) )
        = X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','50'])).

thf('52',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('53',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['30','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4oHAPp930O
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.82  % Solved by: fo/fo7.sh
% 0.64/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.82  % done 684 iterations in 0.356s
% 0.64/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.82  % SZS output start Refutation
% 0.64/0.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.64/0.82  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.64/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.64/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.64/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.64/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.64/0.82  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.64/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.64/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.64/0.82  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.64/0.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.64/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.64/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.82  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.64/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.64/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.82  thf(t42_tex_2, conjecture,
% 0.64/0.82    (![A:$i]:
% 0.64/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.82       ( ![B:$i]:
% 0.64/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.82           ( ( v2_tex_2 @ B @ A ) =>
% 0.64/0.82             ( ![C:$i]:
% 0.64/0.82               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.64/0.82                 ( ( r2_hidden @ C @ B ) =>
% 0.64/0.82                   ( ( k9_subset_1 @
% 0.64/0.82                       ( u1_struct_0 @ A ) @ B @ 
% 0.64/0.82                       ( k2_pre_topc @
% 0.64/0.82                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.64/0.82                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.64/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.82    (~( ![A:$i]:
% 0.64/0.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.64/0.82            ( l1_pre_topc @ A ) ) =>
% 0.64/0.82          ( ![B:$i]:
% 0.64/0.82            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.82              ( ( v2_tex_2 @ B @ A ) =>
% 0.64/0.82                ( ![C:$i]:
% 0.64/0.82                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.64/0.82                    ( ( r2_hidden @ C @ B ) =>
% 0.64/0.82                      ( ( k9_subset_1 @
% 0.64/0.82                          ( u1_struct_0 @ A ) @ B @ 
% 0.64/0.82                          ( k2_pre_topc @
% 0.64/0.82                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.64/0.82                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.64/0.82    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.64/0.82  thf('0', plain,
% 0.64/0.82      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf(t3_subset, axiom,
% 0.64/0.82    (![A:$i,B:$i]:
% 0.64/0.82     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.64/0.82  thf('1', plain,
% 0.64/0.82      (![X41 : $i, X42 : $i]:
% 0.64/0.82         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.64/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.82  thf('2', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.64/0.82      inference('sup-', [status(thm)], ['0', '1'])).
% 0.64/0.82  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf(d2_subset_1, axiom,
% 0.64/0.82    (![A:$i,B:$i]:
% 0.64/0.82     ( ( ( v1_xboole_0 @ A ) =>
% 0.64/0.82         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.64/0.82       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.64/0.82         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.64/0.82  thf('4', plain,
% 0.64/0.82      (![X38 : $i, X39 : $i]:
% 0.64/0.82         (~ (r2_hidden @ X38 @ X39)
% 0.64/0.82          | (m1_subset_1 @ X38 @ X39)
% 0.64/0.82          | (v1_xboole_0 @ X39))),
% 0.64/0.82      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.64/0.82  thf(d1_xboole_0, axiom,
% 0.64/0.82    (![A:$i]:
% 0.64/0.82     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.64/0.82  thf('5', plain,
% 0.64/0.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.64/0.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.82  thf('6', plain,
% 0.64/0.82      (![X38 : $i, X39 : $i]:
% 0.64/0.82         ((m1_subset_1 @ X38 @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 0.64/0.82      inference('clc', [status(thm)], ['4', '5'])).
% 0.64/0.82  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ sk_B_1)),
% 0.64/0.82      inference('sup-', [status(thm)], ['3', '6'])).
% 0.64/0.82  thf(dt_k6_domain_1, axiom,
% 0.64/0.82    (![A:$i,B:$i]:
% 0.64/0.82     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.64/0.82       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.64/0.82  thf('8', plain,
% 0.64/0.82      (![X44 : $i, X45 : $i]:
% 0.64/0.82         ((v1_xboole_0 @ X44)
% 0.64/0.82          | ~ (m1_subset_1 @ X45 @ X44)
% 0.64/0.82          | (m1_subset_1 @ (k6_domain_1 @ X44 @ X45) @ (k1_zfmisc_1 @ X44)))),
% 0.64/0.82      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.64/0.82  thf('9', plain,
% 0.64/0.82      (((m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))
% 0.64/0.82        | (v1_xboole_0 @ sk_B_1))),
% 0.64/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.64/0.82  thf('10', plain, ((m1_subset_1 @ sk_C_1 @ sk_B_1)),
% 0.64/0.82      inference('sup-', [status(thm)], ['3', '6'])).
% 0.64/0.82  thf(redefinition_k6_domain_1, axiom,
% 0.64/0.82    (![A:$i,B:$i]:
% 0.64/0.82     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.64/0.82       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.64/0.82  thf('11', plain,
% 0.64/0.82      (![X46 : $i, X47 : $i]:
% 0.64/0.82         ((v1_xboole_0 @ X46)
% 0.64/0.82          | ~ (m1_subset_1 @ X47 @ X46)
% 0.64/0.82          | ((k6_domain_1 @ X46 @ X47) = (k1_tarski @ X47)))),
% 0.64/0.82      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.64/0.82  thf('12', plain,
% 0.64/0.82      ((((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.64/0.82        | (v1_xboole_0 @ sk_B_1))),
% 0.64/0.82      inference('sup-', [status(thm)], ['10', '11'])).
% 0.64/0.82  thf('13', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('14', plain,
% 0.64/0.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.64/0.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.82  thf('15', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.64/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.64/0.82  thf('16', plain, (((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.64/0.82      inference('clc', [status(thm)], ['12', '15'])).
% 0.64/0.82  thf('17', plain,
% 0.64/0.82      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))
% 0.64/0.82        | (v1_xboole_0 @ sk_B_1))),
% 0.64/0.82      inference('demod', [status(thm)], ['9', '16'])).
% 0.64/0.82  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.64/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.64/0.82  thf('19', plain,
% 0.64/0.82      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.64/0.82      inference('clc', [status(thm)], ['17', '18'])).
% 0.64/0.82  thf('20', plain,
% 0.64/0.82      (![X41 : $i, X42 : $i]:
% 0.64/0.82         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.64/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.82  thf('21', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.64/0.82      inference('sup-', [status(thm)], ['19', '20'])).
% 0.64/0.82  thf(t1_xboole_1, axiom,
% 0.64/0.82    (![A:$i,B:$i,C:$i]:
% 0.64/0.82     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.64/0.82       ( r1_tarski @ A @ C ) ))).
% 0.64/0.82  thf('22', plain,
% 0.64/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.64/0.82         (~ (r1_tarski @ X3 @ X4)
% 0.64/0.82          | ~ (r1_tarski @ X4 @ X5)
% 0.64/0.82          | (r1_tarski @ X3 @ X5))),
% 0.64/0.82      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.64/0.82  thf('23', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         ((r1_tarski @ (k1_tarski @ sk_C_1) @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.64/0.82      inference('sup-', [status(thm)], ['21', '22'])).
% 0.64/0.82  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.64/0.82      inference('sup-', [status(thm)], ['2', '23'])).
% 0.64/0.82  thf(t69_enumset1, axiom,
% 0.64/0.82    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.64/0.82  thf('25', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.64/0.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.64/0.82  thf(t38_zfmisc_1, axiom,
% 0.64/0.82    (![A:$i,B:$i,C:$i]:
% 0.64/0.82     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.64/0.82       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.64/0.82  thf('26', plain,
% 0.64/0.82      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.64/0.82         ((r2_hidden @ X34 @ X35)
% 0.64/0.82          | ~ (r1_tarski @ (k2_tarski @ X34 @ X36) @ X35))),
% 0.64/0.82      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.64/0.82  thf('27', plain,
% 0.64/0.82      (![X0 : $i, X1 : $i]:
% 0.64/0.82         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.64/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.64/0.82  thf('28', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.64/0.82      inference('sup-', [status(thm)], ['24', '27'])).
% 0.64/0.82  thf('29', plain,
% 0.64/0.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.64/0.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.82  thf('30', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.64/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.64/0.82  thf('31', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('32', plain,
% 0.64/0.82      (![X46 : $i, X47 : $i]:
% 0.64/0.82         ((v1_xboole_0 @ X46)
% 0.64/0.82          | ~ (m1_subset_1 @ X47 @ X46)
% 0.64/0.82          | ((k6_domain_1 @ X46 @ X47) = (k1_tarski @ X47)))),
% 0.64/0.82      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.64/0.82  thf('33', plain,
% 0.64/0.82      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.64/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['31', '32'])).
% 0.64/0.82  thf('34', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('35', plain,
% 0.64/0.82      (![X44 : $i, X45 : $i]:
% 0.64/0.82         ((v1_xboole_0 @ X44)
% 0.64/0.82          | ~ (m1_subset_1 @ X45 @ X44)
% 0.64/0.82          | (m1_subset_1 @ (k6_domain_1 @ X44 @ X45) @ (k1_zfmisc_1 @ X44)))),
% 0.64/0.82      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.64/0.82  thf('36', plain,
% 0.64/0.82      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.64/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.64/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.64/0.82  thf('37', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.64/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.64/0.82  thf('38', plain,
% 0.64/0.82      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.82      inference('clc', [status(thm)], ['36', '37'])).
% 0.64/0.82  thf('39', plain,
% 0.64/0.82      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf(t41_tex_2, axiom,
% 0.64/0.82    (![A:$i]:
% 0.64/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.82       ( ![B:$i]:
% 0.64/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.82           ( ( v2_tex_2 @ B @ A ) <=>
% 0.64/0.82             ( ![C:$i]:
% 0.64/0.82               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.82                 ( ( r1_tarski @ C @ B ) =>
% 0.64/0.82                   ( ( k9_subset_1 @
% 0.64/0.82                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.64/0.82                     ( C ) ) ) ) ) ) ) ) ))).
% 0.64/0.82  thf('40', plain,
% 0.64/0.82      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.64/0.82         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.64/0.82          | ~ (v2_tex_2 @ X48 @ X49)
% 0.64/0.82          | ~ (r1_tarski @ X50 @ X48)
% 0.64/0.82          | ((k9_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 0.64/0.82              (k2_pre_topc @ X49 @ X50)) = (X50))
% 0.64/0.82          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.64/0.82          | ~ (l1_pre_topc @ X49)
% 0.64/0.82          | ~ (v2_pre_topc @ X49)
% 0.64/0.82          | (v2_struct_0 @ X49))),
% 0.64/0.82      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.64/0.82  thf('41', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         ((v2_struct_0 @ sk_A)
% 0.64/0.82          | ~ (v2_pre_topc @ sk_A)
% 0.64/0.82          | ~ (l1_pre_topc @ sk_A)
% 0.64/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.64/0.82          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.64/0.82              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.64/0.82          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.64/0.82          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.64/0.82      inference('sup-', [status(thm)], ['39', '40'])).
% 0.64/0.82  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('44', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('45', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         ((v2_struct_0 @ sk_A)
% 0.64/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.64/0.82          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.64/0.82              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.64/0.82          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.64/0.82      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.64/0.82  thf('46', plain,
% 0.64/0.82      ((~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B_1)
% 0.64/0.82        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.64/0.82            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.64/0.82            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.64/0.82        | (v2_struct_0 @ sk_A))),
% 0.64/0.82      inference('sup-', [status(thm)], ['38', '45'])).
% 0.64/0.82  thf('47', plain,
% 0.64/0.82      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.64/0.82         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.64/0.82         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('48', plain,
% 0.64/0.82      ((~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B_1)
% 0.64/0.82        | (v2_struct_0 @ sk_A))),
% 0.64/0.82      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.64/0.82  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('50', plain,
% 0.64/0.82      (~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B_1)),
% 0.64/0.82      inference('clc', [status(thm)], ['48', '49'])).
% 0.64/0.82  thf('51', plain,
% 0.64/0.82      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)
% 0.64/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['33', '50'])).
% 0.64/0.82  thf('52', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.64/0.82      inference('sup-', [status(thm)], ['19', '20'])).
% 0.64/0.82  thf('53', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.64/0.82      inference('demod', [status(thm)], ['51', '52'])).
% 0.64/0.82  thf('54', plain, ($false), inference('demod', [status(thm)], ['30', '53'])).
% 0.64/0.82  
% 0.64/0.82  % SZS output end Refutation
% 0.64/0.82  
% 0.64/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
