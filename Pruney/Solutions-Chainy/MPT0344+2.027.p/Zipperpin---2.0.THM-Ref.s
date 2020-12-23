%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9yzf3KSLXY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:42 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 437 expanded)
%              Number of leaves         :   32 ( 143 expanded)
%              Depth                    :   16
%              Number of atoms          :  562 (3247 expanded)
%              Number of equality atoms :   66 ( 279 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
    | ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t10_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ~ ( ( B != k1_xboole_0 )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ~ ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_subset_1])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ( m1_subset_1 @ X50 @ X51 )
      | ( v1_xboole_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('31',plain,(
    ! [X56: $i] :
      ( ~ ( r2_hidden @ X56 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X56 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['26','37'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('39',plain,(
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X42 ) @ X44 )
      | ~ ( r2_hidden @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('40',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('42',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ ( sk_B @ sk_B_1 ) @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['19','44'])).

thf('46',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('47',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('49',plain,
    ( k1_xboole_0
    = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['29','34'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','49','52'])).

thf('54',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('55',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48 != X47 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X47 ) )
       != ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('56',plain,(
    ! [X47: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X47 ) )
     != ( k1_tarski @ X47 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
 != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('59',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('60',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9yzf3KSLXY
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:39:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 168 iterations in 0.112s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.57  thf(t69_enumset1, axiom,
% 0.36/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.57  thf('0', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf(l51_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (![X45 : $i, X46 : $i]:
% 0.36/0.57         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.36/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.57  thf(t92_xboole_1, axiom,
% 0.36/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.57  thf('3', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.57  thf('4', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.57  thf(t91_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.36/0.57           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['3', '6'])).
% 0.36/0.57  thf(t5_boole, axiom,
% 0.36/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.57  thf('8', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.36/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.57  thf('9', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf(t95_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k3_xboole_0 @ A @ B ) =
% 0.36/0.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ X10 @ X11)
% 0.36/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.36/0.57              (k2_xboole_0 @ X10 @ X11)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.36/0.57           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ X10 @ X11)
% 0.36/0.57           = (k5_xboole_0 @ X10 @ 
% 0.36/0.57              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 0.36/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf(l13_xboole_0, axiom,
% 0.36/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.57  thf('14', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.36/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((k3_xboole_0 @ X1 @ X0) = (X1))
% 0.36/0.57          | ~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['12', '15'])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.36/0.57          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['9', '16'])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      ((~ (v1_xboole_0 @ (k3_tarski @ (k1_tarski @ k1_xboole_0)))
% 0.36/0.57        | ((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['2', '17'])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf(t7_xboole_0, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.57  thf(t10_subset_1, conjecture,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.57       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.57            ( ![C:$i]:
% 0.36/0.57              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i,B:$i]:
% 0.36/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.57          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.57               ( ![C:$i]:
% 0.36/0.57                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 0.36/0.57  thf('21', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(l3_subset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X53 @ X54)
% 0.36/0.57          | (r2_hidden @ X53 @ X55)
% 0.36/0.57          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X55)))),
% 0.36/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['20', '23'])).
% 0.36/0.57  thf('25', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('26', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.36/0.57  thf('27', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.36/0.57  thf(d2_subset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.36/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.36/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.57  thf('28', plain,
% 0.36/0.57      (![X50 : $i, X51 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X50 @ X51)
% 0.36/0.57          | (m1_subset_1 @ X50 @ X51)
% 0.36/0.57          | (v1_xboole_0 @ X51))),
% 0.36/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      (((v1_xboole_0 @ sk_A) | (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (![X56 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X56 @ sk_B_1) | ~ (m1_subset_1 @ X56 @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      ((((sk_B_1) = (k1_xboole_0)) | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.57  thf('33', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('34', plain, (~ (m1_subset_1 @ (sk_B @ sk_B_1) @ sk_A)),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf('35', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.57      inference('clc', [status(thm)], ['29', '34'])).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.57  thf('37', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.57  thf('38', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)),
% 0.36/0.57      inference('demod', [status(thm)], ['26', '37'])).
% 0.36/0.57  thf(l1_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.57  thf('39', plain,
% 0.36/0.57      (![X42 : $i, X44 : $i]:
% 0.36/0.57         ((r1_tarski @ (k1_tarski @ X42) @ X44) | ~ (r2_hidden @ X42 @ X44))),
% 0.36/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.57  thf('40', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.57  thf(t3_xboole_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.57  thf('41', plain,
% 0.36/0.57      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.57  thf('42', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.57  thf(t41_enumset1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k2_tarski @ A @ B ) =
% 0.36/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (![X12 : $i, X13 : $i]:
% 0.36/0.57         ((k2_tarski @ X12 @ X13)
% 0.36/0.57           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k2_tarski @ (sk_B @ sk_B_1) @ X0)
% 0.36/0.57           = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['42', '43'])).
% 0.36/0.57  thf('45', plain,
% 0.36/0.57      (((k1_tarski @ (sk_B @ sk_B_1))
% 0.36/0.57         = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['19', '44'])).
% 0.36/0.57  thf('46', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.57  thf('47', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.57  thf('49', plain, (((k1_xboole_0) = (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.36/0.57  thf('50', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.57      inference('clc', [status(thm)], ['29', '34'])).
% 0.36/0.57  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.57  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['18', '49', '52'])).
% 0.36/0.57  thf('54', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.57  thf(t20_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.57         ( k1_tarski @ A ) ) <=>
% 0.36/0.57       ( ( A ) != ( B ) ) ))).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      (![X47 : $i, X48 : $i]:
% 0.36/0.57         (((X48) != (X47))
% 0.36/0.57          | ((k4_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X47))
% 0.36/0.57              != (k1_tarski @ X48)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      (![X47 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X47))
% 0.36/0.57           != (k1_tarski @ X47))),
% 0.36/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.36/0.57  thf('57', plain,
% 0.36/0.57      (((k4_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 0.36/0.57         != (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['54', '56'])).
% 0.36/0.57  thf('58', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.57  thf('59', plain, (((k1_tarski @ (sk_B @ sk_B_1)) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.57  thf('60', plain,
% 0.36/0.57      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.36/0.57  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf(t100_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.57  thf('62', plain,
% 0.36/0.57      (![X2 : $i, X3 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X2 @ X3)
% 0.36/0.57           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.57  thf('63', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['61', '62'])).
% 0.36/0.57  thf('64', plain,
% 0.36/0.57      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['60', '63'])).
% 0.36/0.57  thf('65', plain, ($false),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['53', '64'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
