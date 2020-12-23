%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bGuCntNlMg

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 617 expanded)
%              Number of leaves         :   19 ( 208 expanded)
%              Depth                    :   14
%              Number of atoms          :  464 (4989 expanded)
%              Number of equality atoms :   31 ( 441 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ ( k1_relat_1 @ X1 ) )
      | ( v5_funct_1 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('7',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','5','8'])).

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

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X6 @ X7 ) @ X8 )
        = X6 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X6 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( ( sk_C_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v5_funct_1 @ k1_xboole_0 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v5_funct_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('23',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('32',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('33',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('37',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ X1 @ X2 ) ) @ ( k1_funct_1 @ X2 @ ( sk_C @ X1 @ X2 ) ) )
      | ( v5_funct_1 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('40',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('42',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('43',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) ) @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( v5_funct_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('50',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( v5_funct_1 @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v5_funct_1 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ X1 ) ),
    inference(clc,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v5_funct_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v5_funct_1 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('56',plain,(
    $false ),
    inference('sup-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bGuCntNlMg
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 41 iterations in 0.050s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(t60_relat_1, axiom,
% 0.21/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.51  thf(d20_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51           ( ( v5_funct_1 @ B @ A ) <=>
% 0.21/0.51             ( ![C:$i]:
% 0.21/0.51               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.51                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_funct_1 @ X1)
% 0.21/0.51          | (r2_hidden @ (sk_C @ X1 @ X2) @ (k1_relat_1 @ X1))
% 0.21/0.51          | (v5_funct_1 @ X1 @ X2)
% 0.21/0.51          | ~ (v1_funct_1 @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.51  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.51  thf(fc3_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('4', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.51  thf('5', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.51  thf('7', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.51  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '5', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '5', '8'])).
% 0.21/0.51  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ?[C:$i]:
% 0.21/0.51       ( ( ![D:$i]:
% 0.21/0.51           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.21/0.51         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.51         ( v1_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (((k1_funct_1 @ (sk_C_1 @ X6 @ X7) @ X8) = (X6))
% 0.21/0.51          | ~ (r2_hidden @ X8 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k1_funct_1 @ (sk_C_1 @ X1 @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ k1_xboole_0 @ X0)) = (X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]: ((k1_relat_1 @ (sk_C_1 @ X6 @ X7)) = (X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.51  thf(t64_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.51          | ((X0) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X0) != (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.21/0.51          | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X1 : $i]:
% 0.21/0.51         (((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf('17', plain, (![X6 : $i, X7 : $i]: (v1_relat_1 @ (sk_C_1 @ X6 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.51  thf('18', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0)) = (X1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0)) = (X1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '18'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((X0) = (X1))
% 0.21/0.51          | ~ (v1_relat_1 @ X2)
% 0.21/0.51          | ~ (v1_funct_1 @ X2)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X2)
% 0.21/0.51          | ~ (v1_funct_1 @ X2)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ X2))),
% 0.21/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v5_funct_1 @ k1_xboole_0 @ X2)
% 0.21/0.51          | ~ (v1_funct_1 @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X2)
% 0.21/0.51          | ((X0) = (X1)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.51  thf(t174_funct_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.21/0.51  thf('23', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X0) = (X1)) | ~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.51  thf('28', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('29', plain, (![X0 : $i]: (v1_relat_1 @ X0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '29'])).
% 0.21/0.51  thf('31', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.51  thf('32', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('33', plain, (![X0 : $i]: (v1_funct_1 @ X0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '33'])).
% 0.21/0.51  thf('35', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0)) = (X1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '18'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_funct_1 @ X1)
% 0.21/0.51          | ~ (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ X1 @ X2)) @ 
% 0.21/0.51               (k1_funct_1 @ X2 @ (sk_C @ X1 @ X2)))
% 0.21/0.51          | (v5_funct_1 @ X1 @ X2)
% 0.21/0.51          | ~ (v1_funct_1 @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r2_hidden @ 
% 0.21/0.51             (k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ k1_xboole_0)) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('40', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('42', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('43', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r2_hidden @ 
% 0.21/0.51             (k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ k1_xboole_0)) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.51          | (v5_funct_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['38', '39', '40', '41', '42', '43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v5_funct_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.51          | ~ (r2_hidden @ 
% 0.21/0.51               (k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ k1_xboole_0)) @ 
% 0.21/0.51               X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1) | (v5_funct_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '46'])).
% 0.21/0.51  thf('48', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.51  thf('49', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.51  thf('50', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain, (![X0 : $i]: ~ (v5_funct_1 @ X0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, (![X0 : $i, X1 : $i]: ~ (v5_funct_1 @ X1 @ X0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.51  thf('53', plain, (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X0 @ X1)),
% 0.21/0.51      inference('clc', [status(thm)], ['47', '52'])).
% 0.21/0.51  thf('54', plain, (![X0 : $i]: (v5_funct_1 @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '53'])).
% 0.21/0.51  thf('55', plain, (![X0 : $i, X1 : $i]: ~ (v5_funct_1 @ X1 @ X0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.51  thf('56', plain, ($false), inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.35/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
