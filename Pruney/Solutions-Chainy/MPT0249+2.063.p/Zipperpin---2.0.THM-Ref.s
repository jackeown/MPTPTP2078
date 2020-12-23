%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTP4psTkIC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  309 ( 552 expanded)
%              Number of equality atoms :   44 (  94 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_tarski @ X12 )
       != ( k2_xboole_0 @ X10 @ X11 ) )
      | ( zip_tseitin_2 @ X11 @ X10 @ X12 )
      | ( zip_tseitin_1 @ X11 @ X10 @ X12 )
      | ( zip_tseitin_0 @ X11 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ( zip_tseitin_0 @ sk_C @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ X0 )
      | ( zip_tseitin_2 @ sk_C @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(eq_res,[status(thm)],['2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k1_tarski @ X7 ) )
      | ~ ( zip_tseitin_2 @ X9 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(eq_res,[status(thm)],['2'])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8
        = ( k1_tarski @ X7 ) )
      | ~ ( zip_tseitin_2 @ X9 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_tarski @ X1 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('10',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('12',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['5','14'])).

thf('16',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('19',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    zip_tseitin_0 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('23',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTP4psTkIC
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:05:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 20 iterations in 0.009s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.46  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t44_zfmisc_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.46          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.46             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.21/0.46  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t43_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.46          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.46          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.46          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.46  thf(zf_stmt_2, axiom,
% 0.21/0.46    (![C:$i,B:$i,A:$i]:
% 0.21/0.46     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.21/0.46       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.46  thf(zf_stmt_4, axiom,
% 0.21/0.46    (![C:$i,B:$i,A:$i]:
% 0.21/0.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.46       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.46  thf(zf_stmt_6, axiom,
% 0.21/0.46    (![C:$i,B:$i,A:$i]:
% 0.21/0.46     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.21/0.46       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_7, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.46          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.21/0.46          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.46          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.46         (((k1_tarski @ X12) != (k2_xboole_0 @ X10 @ X11))
% 0.21/0.46          | (zip_tseitin_2 @ X11 @ X10 @ X12)
% 0.21/0.46          | (zip_tseitin_1 @ X11 @ X10 @ X12)
% 0.21/0.46          | (zip_tseitin_0 @ X11 @ X10 @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k1_tarski @ X0) != (k1_tarski @ sk_A))
% 0.21/0.46          | (zip_tseitin_0 @ sk_C @ sk_B @ X0)
% 0.21/0.46          | (zip_tseitin_1 @ sk_C @ sk_B @ X0)
% 0.21/0.46          | (zip_tseitin_2 @ sk_C @ sk_B @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (((zip_tseitin_2 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.46      inference('eq_res', [status(thm)], ['2'])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.46         (((X9) = (k1_tarski @ X7)) | ~ (zip_tseitin_2 @ X9 @ X8 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (((zip_tseitin_2 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.46      inference('eq_res', [status(thm)], ['2'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.46         (((X8) = (k1_tarski @ X7)) | ~ (zip_tseitin_2 @ X9 @ X8 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (((X2) = (k1_tarski @ X1)) | ~ (zip_tseitin_0 @ X3 @ X2 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((((sk_B) = (k1_tarski @ sk_A)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.46      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.46         (((X4) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X5 @ X4 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((sk_B) = (k1_tarski @ sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | ((sk_C) = (sk_B)))),
% 0.21/0.46      inference('demod', [status(thm)], ['5', '14'])).
% 0.21/0.46  thf('16', plain, (((sk_B) != (sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.46        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.46         (((X4) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X5 @ X4 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.46  thf('20', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('21', plain, ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (((X3) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X3 @ X2 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.46  thf('23', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.46  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('25', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
