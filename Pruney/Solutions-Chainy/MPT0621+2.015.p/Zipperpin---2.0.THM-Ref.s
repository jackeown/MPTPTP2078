%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2K4L2bywXx

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:30 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 160 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  535 (1349 expanded)
%              Number of equality atoms :   65 ( 162 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X10 @ X11 ) @ X12 )
        = X10 )
      | ~ ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X10 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

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

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( ( k1_relat_1 @ X15 )
       != sk_A )
      | ( ( k1_relat_1 @ X16 )
       != sk_A )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('8',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ X13 ) @ X14 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_1 @ X0 ) @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ( ( k7_relat_1 @ X8 @ X9 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k7_relat_1 @ ( sk_B_1 @ X0 ) @ X1 )
        = ( sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k7_relat_1 @ ( sk_B_1 @ X0 ) @ X1 )
        = ( sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('36',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ( ( k7_relat_1 @ X8 @ X9 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( sk_B_1 @ X0 ) @ X0 )
        = ( sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( sk_B_1 @ X0 ) @ X0 )
      = ( sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_xboole_0
      = ( sk_B_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( sk_B_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('48',plain,
    ( k1_xboole_0
    = ( sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('50',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['19','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('58',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2K4L2bywXx
% 0.15/0.37  % Computer   : n023.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:12:51 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 126 iterations in 0.071s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.55  thf(d1_xboole_0, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.55  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ?[C:$i]:
% 0.38/0.55       ( ( ![D:$i]:
% 0.38/0.55           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.38/0.55         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.38/0.55         ( v1_relat_1 @ C ) ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.55         (((k1_funct_1 @ (sk_C_1 @ X10 @ X11) @ X12) = (X10))
% 0.38/0.55          | ~ (r2_hidden @ X12 @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ X0)
% 0.38/0.55          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i]: ((k1_relat_1 @ (sk_C_1 @ X10 @ X11)) = (X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.38/0.55  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ?[B:$i]:
% 0.38/0.55       ( ( ![C:$i]:
% 0.38/0.55           ( ( r2_hidden @ C @ A ) =>
% 0.38/0.55             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.55         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.38/0.55         ( v1_relat_1 @ B ) ) ))).
% 0.38/0.55  thf('4', plain, (![X13 : $i]: ((k1_relat_1 @ (sk_B_1 @ X13)) = (X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf(t16_funct_1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ![B:$i]:
% 0.38/0.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.55               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.38/0.55                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.38/0.55                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.38/0.55       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( ![B:$i]:
% 0.38/0.55            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.55              ( ![C:$i]:
% 0.38/0.55                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.55                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.38/0.55                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.38/0.55                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.38/0.55          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X15 : $i, X16 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X15)
% 0.38/0.55          | ~ (v1_funct_1 @ X15)
% 0.38/0.55          | ((X16) = (X15))
% 0.38/0.55          | ((k1_relat_1 @ X15) != (sk_A))
% 0.38/0.55          | ((k1_relat_1 @ X16) != (sk_A))
% 0.38/0.55          | ~ (v1_funct_1 @ X16)
% 0.38/0.55          | ~ (v1_relat_1 @ X16))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((X0) != (sk_A))
% 0.38/0.55          | ~ (v1_relat_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.38/0.55          | ((X1) = (sk_B_1 @ X0))
% 0.38/0.55          | ~ (v1_funct_1 @ (sk_B_1 @ X0))
% 0.38/0.55          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('7', plain, (![X13 : $i]: (v1_funct_1 @ (sk_B_1 @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('8', plain, (![X13 : $i]: (v1_relat_1 @ (sk_B_1 @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((X0) != (sk_A))
% 0.38/0.55          | ~ (v1_relat_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.38/0.55          | ((X1) = (sk_B_1 @ X0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X1 : $i]:
% 0.38/0.55         (((X1) = (sk_B_1 @ sk_A))
% 0.38/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_relat_1 @ X1))),
% 0.38/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((X0) != (sk_A))
% 0.38/0.55          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.38/0.55          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.38/0.55          | ((sk_C_1 @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['3', '10'])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (sk_C_1 @ X10 @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i]: (v1_funct_1 @ (sk_C_1 @ X10 @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.38/0.55  thf('15', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B_1 @ sk_A))),
% 0.38/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i]:
% 0.38/0.55         (((k1_funct_1 @ (sk_B_1 @ X13) @ X14) = (k1_xboole_0))
% 0.38/0.55          | ~ (r2_hidden @ X14 @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ X0)
% 0.38/0.55          | ((k1_funct_1 @ (sk_B_1 @ X0) @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (k1_xboole_0))
% 0.38/0.55          | (v1_xboole_0 @ sk_A))),
% 0.38/0.55      inference('sup+', [status(thm)], ['15', '18'])).
% 0.38/0.55  thf(t110_relat_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X7 : $i]:
% 0.38/0.55         (((k7_relat_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))
% 0.38/0.55          | ~ (v1_relat_1 @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.38/0.55  thf('21', plain, (![X13 : $i]: ((k1_relat_1 @ (sk_B_1 @ X13)) = (X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf(d3_tarski, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X4 : $i, X6 : $i]:
% 0.38/0.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.55  thf(t97_relat_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ B ) =>
% 0.38/0.55       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.38/0.55         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]:
% 0.38/0.55         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.38/0.55          | ((k7_relat_1 @ X8 @ X9) = (X8))
% 0.38/0.55          | ~ (v1_relat_1 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ (k1_relat_1 @ X1))
% 0.38/0.55          | ~ (v1_relat_1 @ X1)
% 0.38/0.55          | ((k7_relat_1 @ X1 @ X0) = (X1)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ X0)
% 0.38/0.55          | ((k7_relat_1 @ (sk_B_1 @ X0) @ X1) = (sk_B_1 @ X0))
% 0.38/0.55          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['21', '26'])).
% 0.38/0.55  thf('28', plain, (![X13 : $i]: (v1_relat_1 @ (sk_B_1 @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ X0)
% 0.38/0.55          | ((k7_relat_1 @ (sk_B_1 @ X0) @ X1) = (sk_B_1 @ X0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k1_xboole_0) = (sk_B_1 @ X0))
% 0.38/0.55          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.38/0.55          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.55      inference('sup+', [status(thm)], ['20', '29'])).
% 0.38/0.55  thf('31', plain, (![X13 : $i]: (v1_relat_1 @ (sk_B_1 @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (![X0 : $i]: (((k1_xboole_0) = (sk_B_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.55  thf('33', plain, (![X13 : $i]: ((k1_relat_1 @ (sk_B_1 @ X13)) = (X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X0 : $i]: (((k1_relat_1 @ k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (![X7 : $i]:
% 0.38/0.55         (((k7_relat_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))
% 0.38/0.55          | ~ (v1_relat_1 @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.38/0.55  thf('36', plain, (![X13 : $i]: ((k1_relat_1 @ (sk_B_1 @ X13)) = (X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X4 : $i, X6 : $i]:
% 0.38/0.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X4 : $i, X6 : $i]:
% 0.38/0.55         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.55  thf('40', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]:
% 0.38/0.55         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.38/0.55          | ((k7_relat_1 @ X8 @ X9) = (X8))
% 0.38/0.55          | ~ (v1_relat_1 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k7_relat_1 @ (sk_B_1 @ X0) @ X0) = (sk_B_1 @ X0))
% 0.38/0.55          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['36', '42'])).
% 0.38/0.55  thf('44', plain, (![X13 : $i]: (v1_relat_1 @ (sk_B_1 @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      (![X0 : $i]: ((k7_relat_1 @ (sk_B_1 @ X0) @ X0) = (sk_B_1 @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.55  thf('46', plain,
% 0.38/0.55      ((((k1_xboole_0) = (sk_B_1 @ k1_xboole_0))
% 0.38/0.55        | ~ (v1_relat_1 @ (sk_B_1 @ k1_xboole_0)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['35', '45'])).
% 0.38/0.55  thf('47', plain, (![X13 : $i]: (v1_relat_1 @ (sk_B_1 @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('48', plain, (((k1_xboole_0) = (sk_B_1 @ k1_xboole_0))),
% 0.38/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.55  thf('49', plain, (![X13 : $i]: ((k1_relat_1 @ (sk_B_1 @ X13)) = (X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.38/0.55  thf('50', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.55      inference('sup+', [status(thm)], ['48', '49'])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['34', '50'])).
% 0.38/0.55  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('53', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.55  thf('54', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (k1_xboole_0))),
% 0.38/0.55      inference('clc', [status(thm)], ['19', '54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A))),
% 0.38/0.55      inference('sup+', [status(thm)], ['2', '55'])).
% 0.38/0.55  thf('57', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.55  thf('58', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.38/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.38/0.55  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('60', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.55  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
