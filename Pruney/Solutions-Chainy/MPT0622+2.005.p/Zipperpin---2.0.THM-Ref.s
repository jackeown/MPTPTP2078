%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pP83GgcEBa

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 138 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  459 (2120 expanded)
%              Number of equality atoms :   48 ( 295 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t17_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = ( k1_relat_1 @ C ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_tarski @ A ) )
              & ( ( k2_relat_1 @ C )
                = ( k1_tarski @ A ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = ( k1_relat_1 @ C ) )
                & ( ( k2_relat_1 @ B )
                  = ( k1_tarski @ A ) )
                & ( ( k2_relat_1 @ C )
                  = ( k1_tarski @ A ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_B ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_C_2 = sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C_2 = sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    sk_B != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X11 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_B @ sk_C_2 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_funct_1 @ X14 @ ( sk_C_1 @ X13 @ X14 ) )
       != ( k1_funct_1 @ X13 @ ( sk_C_1 @ X13 @ X14 ) ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('29',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_B ) )
    | ( sk_C_2 = sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X11 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('37',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ sk_C_2 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( sk_C_2 = sk_B ) ),
    inference(demod,[status(thm)],['29','37','38','39','40','41','42'])).

thf('44',plain,(
    sk_C_2 = sk_B ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    sk_B != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pP83GgcEBa
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 49 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(t17_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47           ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.47               ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.20/0.47               ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.20/0.47             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47          ( ![C:$i]:
% 0.20/0.47            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47              ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.47                  ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.20/0.47                  ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.20/0.47                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t17_funct_1])).
% 0.20/0.47  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_2))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t9_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.47               ( ![C:$i]:
% 0.20/0.47                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.47                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.47             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X13)
% 0.20/0.47          | ~ (v1_funct_1 @ X13)
% 0.20/0.47          | ((X14) = (X13))
% 0.20/0.47          | (r2_hidden @ (sk_C_1 @ X13 @ X14) @ (k1_relat_1 @ X14))
% 0.20/0.47          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 0.20/0.47          | ~ (v1_funct_1 @ X14)
% 0.20/0.47          | ~ (v1_relat_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ sk_C_2)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 0.20/0.47          | ((sk_C_2) = (X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_2))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.20/0.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_B))
% 0.20/0.47          | ((sk_C_2) = (X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ((sk_C_2) = (sk_B))
% 0.20/0.47        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['6'])).
% 0.20/0.47  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((((sk_C_2) = (sk_B))
% 0.20/0.47        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.47  thf('11', plain, (((sk_B) != (sk_C_2))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ (k1_relat_1 @ sk_B))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_2))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t12_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ X12 @ X11) @ (k2_relat_1 @ X12))
% 0.20/0.47          | ~ (v1_funct_1 @ X12)
% 0.20/0.47          | ~ (v1_relat_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.47          | ~ (v1_relat_1 @ sk_C_2)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, (((k2_relat_1 @ sk_B) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.47      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16', '17', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 0.20/0.47        (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '21'])).
% 0.20/0.47  thf('23', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d1_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i, X3 : $i]:
% 0.20/0.47         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_B @ sk_C_2)) = (sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X13)
% 0.20/0.47          | ~ (v1_funct_1 @ X13)
% 0.20/0.47          | ((X14) = (X13))
% 0.20/0.47          | ((k1_funct_1 @ X14 @ (sk_C_1 @ X13 @ X14))
% 0.20/0.47              != (k1_funct_1 @ X13 @ (sk_C_1 @ X13 @ X14)))
% 0.20/0.47          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 0.20/0.47          | ~ (v1_funct_1 @ X14)
% 0.20/0.47          | ~ (v1_relat_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ sk_C_2)))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C_2)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.47        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_B))
% 0.20/0.47        | ((sk_C_2) = (sk_B))
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ (k1_relat_1 @ sk_B))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ X12 @ X11) @ (k2_relat_1 @ X12))
% 0.20/0.47          | ~ (v1_funct_1 @ X12)
% 0.20/0.47          | ~ (v1_relat_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 0.20/0.47           (k2_relat_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 0.20/0.47        (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.47  thf('37', plain, (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ sk_C_2)) = (sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('39', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('40', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_2))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      ((((sk_A) != (sk_A))
% 0.20/0.47        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.20/0.47        | ((sk_C_2) = (sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['29', '37', '38', '39', '40', '41', '42'])).
% 0.20/0.47  thf('44', plain, (((sk_C_2) = (sk_B))),
% 0.20/0.47      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.47  thf('45', plain, (((sk_B) != (sk_C_2))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('46', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
