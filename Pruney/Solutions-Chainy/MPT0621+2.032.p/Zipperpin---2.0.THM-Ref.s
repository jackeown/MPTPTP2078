%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S8XGnJY1l3

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 261 expanded)
%              Number of leaves         :   16 (  90 expanded)
%              Depth                    :   17
%              Number of atoms          :  520 (2744 expanded)
%              Number of equality atoms :   74 ( 401 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( ( k1_relat_1 @ X11 )
       != sk_A )
      | ( ( k1_relat_1 @ X12 )
       != sk_A )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
       != sk_A )
      | ( X2
        = ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
       != sk_A )
      | ( X2
        = ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2
        = ( sk_C_1 @ X1 @ sk_A ) )
      | ( ( k1_relat_1 @ X2 )
       != sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_C_1 @ X2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_C_1 @ X2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_C_1 @ X2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( X1
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','23','26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
        = X1 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = X1 ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = X1 ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S8XGnJY1l3
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:16:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 39 iterations in 0.028s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ?[C:$i]:
% 0.19/0.48       ( ( ![D:$i]:
% 0.19/0.48           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.19/0.48         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( v1_relat_1 @ C ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]: ((k1_relat_1 @ (sk_C_1 @ X8 @ X9)) = (X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]: ((k1_relat_1 @ (sk_C_1 @ X8 @ X9)) = (X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf(t16_funct_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ![B:$i]:
% 0.19/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.48                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.48                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ![B:$i]:
% 0.19/0.48            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.48                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.48                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.48          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X11)
% 0.19/0.48          | ~ (v1_funct_1 @ X11)
% 0.19/0.48          | ((X12) = (X11))
% 0.19/0.48          | ((k1_relat_1 @ X11) != (sk_A))
% 0.19/0.48          | ((k1_relat_1 @ X12) != (sk_A))
% 0.19/0.48          | ~ (v1_funct_1 @ X12)
% 0.19/0.48          | ~ (v1_relat_1 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X0) != (sk_A))
% 0.19/0.48          | ~ (v1_relat_1 @ X2)
% 0.19/0.48          | ~ (v1_funct_1 @ X2)
% 0.19/0.48          | ((k1_relat_1 @ X2) != (sk_A))
% 0.19/0.48          | ((X2) = (sk_C_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf('4', plain, (![X8 : $i, X9 : $i]: (v1_funct_1 @ (sk_C_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('5', plain, (![X8 : $i, X9 : $i]: (v1_relat_1 @ (sk_C_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X0) != (sk_A))
% 0.19/0.48          | ~ (v1_relat_1 @ X2)
% 0.19/0.48          | ~ (v1_funct_1 @ X2)
% 0.19/0.48          | ((k1_relat_1 @ X2) != (sk_A))
% 0.19/0.48          | ((X2) = (sk_C_1 @ X1 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         (((X2) = (sk_C_1 @ X1 @ sk_A))
% 0.19/0.48          | ((k1_relat_1 @ X2) != (sk_A))
% 0.19/0.48          | ~ (v1_funct_1 @ X2)
% 0.19/0.48          | ~ (v1_relat_1 @ X2))),
% 0.19/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X0) != (sk_A))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.48          | ((sk_C_1 @ X1 @ X0) = (sk_C_1 @ X2 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '7'])).
% 0.19/0.48  thf('9', plain, (![X8 : $i, X9 : $i]: (v1_relat_1 @ (sk_C_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('10', plain, (![X8 : $i, X9 : $i]: (v1_funct_1 @ (sk_C_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_C_1 @ X2 @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_C_1 @ X2 @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.48  thf(t60_relat_1, axiom,
% 0.19/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('13', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf(d5_funct_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.48               ( ?[D:$i]:
% 0.19/0.48                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.19/0.48                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 0.19/0.48          | (r2_hidden @ (sk_D @ X1 @ X2) @ (k1_relat_1 @ X2))
% 0.19/0.48          | ((X1) = (k2_relat_1 @ X2))
% 0.19/0.48          | ~ (v1_funct_1 @ X2)
% 0.19/0.48          | ~ (v1_relat_1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.48          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.48          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.48          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]: ((k1_relat_1 @ (sk_C_1 @ X8 @ X9)) = (X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf(t64_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.48           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((X0) != (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.48          | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain, (![X8 : $i, X9 : $i]: (v1_relat_1 @ (sk_C_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((X0) != (k1_xboole_0)) | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.48  thf('22', plain, (![X8 : $i, X9 : $i]: (v1_relat_1 @ (sk_C_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.48      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf('24', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.48  thf('25', plain, (![X8 : $i, X9 : $i]: (v1_funct_1 @ (sk_C_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('26', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.19/0.48      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['15', '23', '26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.19/0.48          | ~ (r2_hidden @ X10 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | ((k1_funct_1 @ (sk_C_1 @ X1 @ k1_xboole_0) @ 
% 0.19/0.48              (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('31', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 0.19/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 0.19/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X0) = (X1))
% 0.19/0.48          | ((X2) = (k1_xboole_0))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X2 @ k1_xboole_0) @ X2)
% 0.19/0.48          | ((X2) = (k1_xboole_0))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X2 @ k1_xboole_0) @ X2))),
% 0.19/0.48      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X2 @ k1_xboole_0) @ X2)
% 0.19/0.48          | ((X2) = (k1_xboole_0))
% 0.19/0.48          | ((X0) = (X1)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('condensation', [status(thm)], ['35'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.19/0.48          | ~ (r2_hidden @ X10 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.19/0.48              = (X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.19/0.48            = (X1))
% 0.19/0.48          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['12', '38'])).
% 0.19/0.48  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.19/0.48           = (X1))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.19/0.48           = (X1))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('43', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['41', '42'])).
% 0.19/0.48  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('45', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.48  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
