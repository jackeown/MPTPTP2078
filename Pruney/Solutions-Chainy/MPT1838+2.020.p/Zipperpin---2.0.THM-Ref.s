%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mlY31IMzzp

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:17 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  520 (1049 expanded)
%              Number of equality atoms :   46 (  67 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X9
       != ( k2_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k2_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ sk_A ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B_2 @ sk_A ) @ sk_B_2 )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B_2 @ sk_A ) @ sk_B_2 ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X10 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k2_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k2_xboole_0 @ X10 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X10 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['15','24'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X25: $i] :
      ( ~ ( v1_zfmisc_1 @ X25 )
      | ( X25
        = ( k6_domain_1 @ X25 @ ( sk_B_1 @ X25 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('27',plain,(
    ! [X25: $i] :
      ( ~ ( v1_zfmisc_1 @ X25 )
      | ( m1_subset_1 @ ( sk_B_1 @ X25 ) @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X18 = X19 )
      | ( ( k1_tarski @ X20 )
       != ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X2 = X1 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = X1 )
      | ~ ( v1_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) )
      | ( v1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ sk_B_2 @ sk_A ) )
    | ( sk_B_2 = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['15','24'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2 = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mlY31IMzzp
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:22:53 EST 2020
% 0.21/0.36  % CPUTime    : 
% 0.21/0.36  % Running portfolio for 600 s
% 0.21/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 1.06/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.28  % Solved by: fo/fo7.sh
% 1.06/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.28  % done 2064 iterations in 0.816s
% 1.06/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.28  % SZS output start Refutation
% 1.06/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.06/1.28  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.28  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.06/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.28  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.06/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.28  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.06/1.28  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.06/1.28  thf(t1_tex_2, conjecture,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.06/1.28           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.28    (~( ![A:$i]:
% 1.06/1.28        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.28          ( ![B:$i]:
% 1.06/1.28            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.06/1.28              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 1.06/1.28    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 1.06/1.28  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.06/1.28  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.28  thf(d3_tarski, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( r1_tarski @ A @ B ) <=>
% 1.06/1.28       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.06/1.28  thf('2', plain,
% 1.06/1.28      (![X4 : $i, X6 : $i]:
% 1.06/1.28         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf(d3_xboole_0, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.06/1.28       ( ![D:$i]:
% 1.06/1.28         ( ( r2_hidden @ D @ C ) <=>
% 1.06/1.28           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.06/1.28  thf('3', plain,
% 1.06/1.28      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X11 @ X9)
% 1.06/1.28          | (r2_hidden @ X11 @ X10)
% 1.06/1.28          | (r2_hidden @ X11 @ X8)
% 1.06/1.28          | ((X9) != (k2_xboole_0 @ X10 @ X8)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.06/1.28  thf('4', plain,
% 1.06/1.28      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.06/1.28         ((r2_hidden @ X11 @ X8)
% 1.06/1.28          | (r2_hidden @ X11 @ X10)
% 1.06/1.28          | ~ (r2_hidden @ X11 @ (k2_xboole_0 @ X10 @ X8)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['3'])).
% 1.06/1.28  thf('5', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.06/1.28          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 1.06/1.28          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['2', '4'])).
% 1.06/1.28  thf('6', plain,
% 1.06/1.28      (![X4 : $i, X6 : $i]:
% 1.06/1.28         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('7', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X1)
% 1.06/1.28          | (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 1.06/1.28          | (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['5', '6'])).
% 1.06/1.28  thf('8', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 1.06/1.28          | (r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X1))),
% 1.06/1.28      inference('simplify', [status(thm)], ['7'])).
% 1.06/1.28  thf('9', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('10', plain,
% 1.06/1.28      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X3 @ X4)
% 1.06/1.28          | (r2_hidden @ X3 @ X5)
% 1.06/1.28          | ~ (r1_tarski @ X4 @ X5))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('11', plain,
% 1.06/1.28      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.28  thf('12', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((r1_tarski @ (k2_xboole_0 @ X0 @ sk_A) @ X0)
% 1.06/1.28          | (r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ sk_A)) @ sk_B_2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['8', '11'])).
% 1.06/1.28  thf('13', plain,
% 1.06/1.28      (![X4 : $i, X6 : $i]:
% 1.06/1.28         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('14', plain,
% 1.06/1.28      (((r1_tarski @ (k2_xboole_0 @ sk_B_2 @ sk_A) @ sk_B_2)
% 1.06/1.28        | (r1_tarski @ (k2_xboole_0 @ sk_B_2 @ sk_A) @ sk_B_2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['12', '13'])).
% 1.06/1.28  thf('15', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B_2 @ sk_A) @ sk_B_2)),
% 1.06/1.28      inference('simplify', [status(thm)], ['14'])).
% 1.06/1.28  thf('16', plain,
% 1.06/1.28      (![X4 : $i, X6 : $i]:
% 1.06/1.28         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('17', plain,
% 1.06/1.28      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X7 @ X10)
% 1.06/1.28          | (r2_hidden @ X7 @ X9)
% 1.06/1.28          | ((X9) != (k2_xboole_0 @ X10 @ X8)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.06/1.28  thf('18', plain,
% 1.06/1.28      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.06/1.28         ((r2_hidden @ X7 @ (k2_xboole_0 @ X10 @ X8))
% 1.06/1.28          | ~ (r2_hidden @ X7 @ X10))),
% 1.06/1.28      inference('simplify', [status(thm)], ['17'])).
% 1.06/1.28  thf('19', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         ((r1_tarski @ X0 @ X1)
% 1.06/1.28          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['16', '18'])).
% 1.06/1.28  thf('20', plain,
% 1.06/1.28      (![X4 : $i, X6 : $i]:
% 1.06/1.28         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('21', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.06/1.28          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.28  thf('22', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['21'])).
% 1.06/1.28  thf(d10_xboole_0, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.28  thf('23', plain,
% 1.06/1.28      (![X13 : $i, X15 : $i]:
% 1.06/1.28         (((X13) = (X15))
% 1.06/1.28          | ~ (r1_tarski @ X15 @ X13)
% 1.06/1.28          | ~ (r1_tarski @ X13 @ X15))),
% 1.06/1.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.28  thf('24', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.06/1.28          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['22', '23'])).
% 1.06/1.28  thf('25', plain, (((k2_xboole_0 @ sk_B_2 @ sk_A) = (sk_B_2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['15', '24'])).
% 1.06/1.28  thf(d1_tex_2, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.28       ( ( v1_zfmisc_1 @ A ) <=>
% 1.06/1.28         ( ?[B:$i]:
% 1.06/1.28           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 1.06/1.28  thf('26', plain,
% 1.06/1.28      (![X25 : $i]:
% 1.06/1.28         (~ (v1_zfmisc_1 @ X25)
% 1.06/1.28          | ((X25) = (k6_domain_1 @ X25 @ (sk_B_1 @ X25)))
% 1.06/1.28          | (v1_xboole_0 @ X25))),
% 1.06/1.28      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.06/1.28  thf('27', plain,
% 1.06/1.28      (![X25 : $i]:
% 1.06/1.28         (~ (v1_zfmisc_1 @ X25)
% 1.06/1.28          | (m1_subset_1 @ (sk_B_1 @ X25) @ X25)
% 1.06/1.28          | (v1_xboole_0 @ X25))),
% 1.06/1.28      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.06/1.28  thf(redefinition_k6_domain_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.06/1.28       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.06/1.28  thf('28', plain,
% 1.06/1.28      (![X23 : $i, X24 : $i]:
% 1.06/1.28         ((v1_xboole_0 @ X23)
% 1.06/1.28          | ~ (m1_subset_1 @ X24 @ X23)
% 1.06/1.28          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.06/1.28  thf('29', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v1_zfmisc_1 @ X0)
% 1.06/1.28          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.06/1.28          | (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['27', '28'])).
% 1.06/1.28  thf('30', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.06/1.28          | ~ (v1_zfmisc_1 @ X0)
% 1.06/1.28          | (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['29'])).
% 1.06/1.28  thf('31', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.06/1.28          | (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v1_zfmisc_1 @ X0)
% 1.06/1.28          | (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v1_zfmisc_1 @ X0))),
% 1.06/1.28      inference('sup+', [status(thm)], ['26', '30'])).
% 1.06/1.28  thf('32', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (v1_zfmisc_1 @ X0)
% 1.06/1.28          | (v1_xboole_0 @ X0)
% 1.06/1.28          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 1.06/1.28      inference('simplify', [status(thm)], ['31'])).
% 1.06/1.28  thf(t44_zfmisc_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.06/1.28          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.06/1.28          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 1.06/1.28  thf('33', plain,
% 1.06/1.28      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.28         (((X18) = (k1_xboole_0))
% 1.06/1.28          | ((X19) = (k1_xboole_0))
% 1.06/1.28          | ((X18) = (X19))
% 1.06/1.28          | ((k1_tarski @ X20) != (k2_xboole_0 @ X18 @ X19)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 1.06/1.28  thf('34', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 1.06/1.28          | (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v1_zfmisc_1 @ X0)
% 1.06/1.28          | ((X2) = (X1))
% 1.06/1.28          | ((X1) = (k1_xboole_0))
% 1.06/1.28          | ((X2) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('35', plain,
% 1.06/1.28      (![X1 : $i, X2 : $i]:
% 1.06/1.28         (((X2) = (k1_xboole_0))
% 1.06/1.28          | ((X1) = (k1_xboole_0))
% 1.06/1.28          | ((X2) = (X1))
% 1.06/1.28          | ~ (v1_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1))
% 1.06/1.28          | (v1_xboole_0 @ (k2_xboole_0 @ X2 @ X1)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['34'])).
% 1.06/1.28  thf('36', plain,
% 1.06/1.28      ((~ (v1_zfmisc_1 @ sk_B_2)
% 1.06/1.28        | (v1_xboole_0 @ (k2_xboole_0 @ sk_B_2 @ sk_A))
% 1.06/1.28        | ((sk_B_2) = (sk_A))
% 1.06/1.28        | ((sk_A) = (k1_xboole_0))
% 1.06/1.28        | ((sk_B_2) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['25', '35'])).
% 1.06/1.28  thf('37', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('38', plain, (((k2_xboole_0 @ sk_B_2 @ sk_A) = (sk_B_2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['15', '24'])).
% 1.06/1.28  thf('39', plain,
% 1.06/1.28      (((v1_xboole_0 @ sk_B_2)
% 1.06/1.28        | ((sk_B_2) = (sk_A))
% 1.06/1.28        | ((sk_A) = (k1_xboole_0))
% 1.06/1.28        | ((sk_B_2) = (k1_xboole_0)))),
% 1.06/1.28      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.06/1.28  thf('40', plain, (((sk_A) != (sk_B_2))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('41', plain,
% 1.06/1.28      (((v1_xboole_0 @ sk_B_2)
% 1.06/1.28        | ((sk_A) = (k1_xboole_0))
% 1.06/1.28        | ((sk_B_2) = (k1_xboole_0)))),
% 1.06/1.28      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 1.06/1.28  thf('42', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('43', plain, ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.06/1.28      inference('clc', [status(thm)], ['41', '42'])).
% 1.06/1.28  thf('44', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('45', plain,
% 1.06/1.28      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['43', '44'])).
% 1.06/1.28  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.28  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 1.06/1.28      inference('demod', [status(thm)], ['45', '46'])).
% 1.06/1.28  thf('48', plain, ((v1_xboole_0 @ sk_A)),
% 1.06/1.28      inference('demod', [status(thm)], ['1', '47'])).
% 1.06/1.28  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
