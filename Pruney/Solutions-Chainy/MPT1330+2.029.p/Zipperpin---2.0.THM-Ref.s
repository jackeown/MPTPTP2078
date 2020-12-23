%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TzGVJUPYjA

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 148 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  617 (2622 expanded)
%              Number of equality atoms :   63 ( 228 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( ( k8_relset_1 @ X0 @ X2 @ X1 @ X2 )
        = X0 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('10',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','19','20'])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( ( k8_relset_1 @ X0 @ X2 @ X1 @ X2 )
        = X0 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ k1_xboole_0 @ X2 @ X1 @ X2 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X1 @ k1_xboole_0 @ X2 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf('36',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('47',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['38','47'])).

thf('49',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('50',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('54',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','51','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TzGVJUPYjA
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 34 iterations in 0.017s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(d3_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X3 : $i]:
% 0.21/0.47         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X3 : $i]:
% 0.21/0.47         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.47  thf(t52_tops_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( l1_struct_0 @ B ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.47                 ( m1_subset_1 @
% 0.21/0.47                   C @ 
% 0.21/0.47                   ( k1_zfmisc_1 @
% 0.21/0.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.47               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.47                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.47                 ( ( k8_relset_1 @
% 0.21/0.47                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.47                     ( k2_struct_0 @ B ) ) =
% 0.21/0.47                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( l1_struct_0 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( l1_struct_0 @ B ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.47                    ( v1_funct_2 @
% 0.21/0.47                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.47                    ( m1_subset_1 @
% 0.21/0.47                      C @ 
% 0.21/0.47                      ( k1_zfmisc_1 @
% 0.21/0.47                        ( k2_zfmisc_1 @
% 0.21/0.47                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.47                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.47                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.47                    ( ( k8_relset_1 @
% 0.21/0.47                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.47                        ( k2_struct_0 @ B ) ) =
% 0.21/0.47                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((m1_subset_1 @ sk_C @ 
% 0.21/0.47         (k1_zfmisc_1 @ 
% 0.21/0.47          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.21/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (((m1_subset_1 @ sk_C @ 
% 0.21/0.47         (k1_zfmisc_1 @ 
% 0.21/0.47          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.47        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup+', [status(thm)], ['0', '5'])).
% 0.21/0.47  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf(t48_funct_2, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.47       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.47         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((X2) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ~ (v1_funct_2 @ X1 @ X0 @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.21/0.47          | ((k8_relset_1 @ X0 @ X2 @ X1 @ X2) = (X0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47          (k2_struct_0 @ sk_B)) = (k2_struct_0 @ sk_A))
% 0.21/0.47        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.47        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X3 : $i]:
% 0.21/0.47         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X3 : $i]:
% 0.21/0.47         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.47        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup+', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47          (k2_struct_0 @ sk_B)) = (k2_struct_0 @ sk_A))
% 0.21/0.47        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.47        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X3 : $i]:
% 0.21/0.47         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['22'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (((m1_subset_1 @ sk_C @ 
% 0.21/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((X0) != (k1_xboole_0))
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ~ (v1_funct_2 @ X1 @ X0 @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.21/0.47          | ((k8_relset_1 @ X0 @ X2 @ X1 @ X2) = (X0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         (((k8_relset_1 @ k1_xboole_0 @ X2 @ X1 @ X2) = (k1_xboole_0))
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X2)))
% 0.21/0.47          | ~ (v1_funct_2 @ X1 @ k1_xboole_0 @ X2)
% 0.21/0.47          | ~ (v1_funct_1 @ X1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (((~ (v1_funct_1 @ sk_C)
% 0.21/0.47         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.47         | ((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47             (u1_struct_0 @ sk_B)) = (k1_xboole_0))))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['27', '29'])).
% 0.21/0.47  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['22'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47          (u1_struct_0 @ sk_B)) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47           (k2_struct_0 @ sk_B)) = (k1_xboole_0))
% 0.21/0.47         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['24', '35'])).
% 0.21/0.47  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47          (k2_struct_0 @ sk_B)) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['22'])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X3 : $i]:
% 0.21/0.47         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.21/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.47  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['39', '44'])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['22'])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.21/0.47         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.47  thf('48', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['38', '47'])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.21/0.47       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['22'])).
% 0.21/0.47  thf('50', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.21/0.47  thf('51', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['23', '50'])).
% 0.21/0.47  thf('52', plain,
% 0.21/0.47      (![X3 : $i]:
% 0.21/0.47         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.47  thf('54', plain,
% 0.21/0.47      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.21/0.47        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.47  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('56', plain,
% 0.21/0.47      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.47         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.47  thf('57', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['21', '51', '56'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
