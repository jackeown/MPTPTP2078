%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vrEgHO9DAI

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 228 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  578 (2422 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(t52_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ A @ B )
                  & ( r4_wellord1 @ B @ C ) )
               => ( r4_wellord1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( ( ( r4_wellord1 @ A @ B )
                    & ( r4_wellord1 @ B @ C ) )
                 => ( r4_wellord1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_wellord1])).

thf('2',plain,(
    r4_wellord1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
          <=> ? [C: $i] :
                ( ( r3_wellord1 @ A @ B @ C )
                & ( v1_funct_1 @ C )
                & ( v1_relat_1 @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ X3 @ X2 )
      | ( r3_wellord1 @ X3 @ X2 @ ( sk_C @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r3_wellord1 @ sk_B @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r3_wellord1 @ sk_B @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ X3 @ X2 )
      | ( r3_wellord1 @ X3 @ X2 @ ( sk_C @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t51_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( ( v1_relat_1 @ D )
                    & ( v1_funct_1 @ D ) )
                 => ! [E: $i] :
                      ( ( ( v1_relat_1 @ E )
                        & ( v1_funct_1 @ E ) )
                     => ( ( ( r3_wellord1 @ A @ B @ D )
                          & ( r3_wellord1 @ B @ C @ E ) )
                       => ( r3_wellord1 @ A @ C @ ( k5_relat_1 @ D @ E ) ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r3_wellord1 @ X7 @ X5 @ X6 )
      | ~ ( r3_wellord1 @ X5 @ X8 @ X9 )
      | ( r3_wellord1 @ X7 @ X8 @ ( k5_relat_1 @ X6 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t51_wellord1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r3_wellord1 @ sk_A @ X0 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ~ ( r3_wellord1 @ sk_B @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ X3 @ X2 )
      | ( v1_funct_1 @ ( sk_C @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ X3 @ X2 )
      | ( v1_relat_1 @ ( sk_C @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r3_wellord1 @ sk_A @ X0 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ~ ( r3_wellord1 @ sk_B @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','22','28','29'])).

thf('31',plain,
    ( ( r3_wellord1 @ sk_A @ sk_C_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,(
    r4_wellord1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ X3 @ X2 )
      | ( v1_funct_1 @ ( sk_C @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    r4_wellord1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ X3 @ X2 )
      | ( v1_relat_1 @ ( sk_C @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r3_wellord1 @ sk_A @ sk_C_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','37','43','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r3_wellord1 @ X3 @ X2 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ( r4_wellord1 @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r4_wellord1 @ sk_A @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r4_wellord1 @ sk_A @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( r4_wellord1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','52'])).

thf('54',plain,(
    v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('55',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('56',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('57',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('58',plain,(
    ~ ( v1_relat_1 @ ( k5_relat_1 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    v1_funct_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('61',plain,(
    v1_relat_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('62',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('63',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vrEgHO9DAI
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 22 iterations in 0.017s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.47  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.21/0.47  thf(fc2_funct_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.21/0.47         ( v1_funct_1 @ B ) ) =>
% 0.21/0.47       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.21/0.47         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_funct_1 @ X1)
% 0.21/0.48          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_funct_1 @ X1)
% 0.21/0.48          | (v1_funct_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.21/0.48  thf(t52_wellord1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( v1_relat_1 @ C ) =>
% 0.21/0.48               ( ( ( r4_wellord1 @ A @ B ) & ( r4_wellord1 @ B @ C ) ) =>
% 0.21/0.48                 ( r4_wellord1 @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( v1_relat_1 @ B ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( v1_relat_1 @ C ) =>
% 0.21/0.48                  ( ( ( r4_wellord1 @ A @ B ) & ( r4_wellord1 @ B @ C ) ) =>
% 0.21/0.48                    ( r4_wellord1 @ A @ C ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t52_wellord1])).
% 0.21/0.48  thf('2', plain, ((r4_wellord1 @ sk_B @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d8_wellord1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ( r4_wellord1 @ A @ B ) <=>
% 0.21/0.48             ( ?[C:$i]:
% 0.21/0.48               ( ( r3_wellord1 @ A @ B @ C ) & ( v1_funct_1 @ C ) & 
% 0.21/0.48                 ( v1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X2)
% 0.21/0.48          | ~ (r4_wellord1 @ X3 @ X2)
% 0.21/0.48          | (r3_wellord1 @ X3 @ X2 @ (sk_C @ X2 @ X3))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.48        | (r3_wellord1 @ sk_B @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((r3_wellord1 @ sk_B @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.48  thf('8', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X2)
% 0.21/0.48          | ~ (r4_wellord1 @ X3 @ X2)
% 0.21/0.48          | (r3_wellord1 @ X3 @ X2 @ (sk_C @ X2 @ X3))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | (r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, ((r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.48  thf(t51_wellord1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( v1_relat_1 @ C ) =>
% 0.21/0.48               ( ![D:$i]:
% 0.21/0.48                 ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.48                   ( ![E:$i]:
% 0.21/0.48                     ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.21/0.48                       ( ( ( r3_wellord1 @ A @ B @ D ) & 
% 0.21/0.48                           ( r3_wellord1 @ B @ C @ E ) ) =>
% 0.21/0.48                         ( r3_wellord1 @ A @ C @ ( k5_relat_1 @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X6)
% 0.21/0.48          | ~ (v1_funct_1 @ X6)
% 0.21/0.48          | ~ (r3_wellord1 @ X7 @ X5 @ X6)
% 0.21/0.48          | ~ (r3_wellord1 @ X5 @ X8 @ X9)
% 0.21/0.48          | (r3_wellord1 @ X7 @ X8 @ (k5_relat_1 @ X6 @ X9))
% 0.21/0.48          | ~ (v1_funct_1 @ X9)
% 0.21/0.48          | ~ (v1_relat_1 @ X9)
% 0.21/0.48          | ~ (v1_relat_1 @ X8)
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t51_wellord1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ sk_A)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_funct_1 @ X1)
% 0.21/0.48          | (r3_wellord1 @ sk_A @ X0 @ (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ X1))
% 0.21/0.48          | ~ (r3_wellord1 @ sk_B @ X0 @ X1)
% 0.21/0.48          | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.48          | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.48          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X2)
% 0.21/0.48          | ~ (r4_wellord1 @ X3 @ X2)
% 0.21/0.48          | (v1_funct_1 @ (sk_C @ X2 @ X3))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.48  thf('23', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X2)
% 0.21/0.48          | ~ (r4_wellord1 @ X3 @ X2)
% 0.21/0.48          | (v1_relat_1 @ (sk_C @ X2 @ X3))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.48  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_funct_1 @ X1)
% 0.21/0.48          | (r3_wellord1 @ sk_A @ X0 @ (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ X1))
% 0.21/0.48          | ~ (r3_wellord1 @ sk_B @ X0 @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16', '22', '28', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((r3_wellord1 @ sk_A @ sk_C_1 @ 
% 0.21/0.48         (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.21/0.48        | ~ (v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '30'])).
% 0.21/0.48  thf('32', plain, ((r4_wellord1 @ sk_B @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X2)
% 0.21/0.48          | ~ (r4_wellord1 @ X3 @ X2)
% 0.21/0.48          | (v1_funct_1 @ (sk_C @ X2 @ X3))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.48        | (v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('37', plain, ((v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.48  thf('38', plain, ((r4_wellord1 @ sk_B @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X2)
% 0.21/0.48          | ~ (r4_wellord1 @ X3 @ X2)
% 0.21/0.48          | (v1_relat_1 @ (sk_C @ X2 @ X3))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.48        | (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('43', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.48  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((r3_wellord1 @ sk_A @ sk_C_1 @ 
% 0.21/0.48        (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '37', '43', '44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X2)
% 0.21/0.48          | ~ (r3_wellord1 @ X3 @ X2 @ X4)
% 0.21/0.48          | ~ (v1_funct_1 @ X4)
% 0.21/0.48          | ~ (v1_relat_1 @ X4)
% 0.21/0.48          | (r4_wellord1 @ X3 @ X2)
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | (r4_wellord1 @ sk_A @ sk_C_1)
% 0.21/0.48        | ~ (v1_relat_1 @ 
% 0.21/0.48             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.21/0.48        | ~ (v1_funct_1 @ 
% 0.21/0.48             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.48  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (((r4_wellord1 @ sk_A @ sk_C_1)
% 0.21/0.48        | ~ (v1_relat_1 @ 
% 0.21/0.48             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.21/0.48        | ~ (v1_funct_1 @ 
% 0.21/0.48             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.48  thf('51', plain, (~ (r4_wellord1 @ sk_A @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ 
% 0.21/0.48           (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))
% 0.21/0.48        | ~ (v1_relat_1 @ 
% 0.21/0.48             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))),
% 0.21/0.48      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ 
% 0.21/0.48             (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '52'])).
% 0.21/0.48  thf('54', plain, ((v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.48  thf('55', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.48  thf('56', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.48  thf('57', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      (~ (v1_relat_1 @ 
% 0.21/0.48          (k5_relat_1 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_C_1 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '58'])).
% 0.21/0.48  thf('60', plain, ((v1_funct_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.48  thf('61', plain, ((v1_relat_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.48  thf('62', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.48  thf('63', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.48  thf('64', plain, ($false),
% 0.21/0.48      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
