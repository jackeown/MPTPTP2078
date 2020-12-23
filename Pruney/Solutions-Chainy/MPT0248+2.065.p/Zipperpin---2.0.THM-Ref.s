%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AEuMpYoJR4

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:27 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 271 expanded)
%              Number of leaves         :   22 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  660 (2953 expanded)
%              Number of equality atoms :  127 ( 641 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ X5 @ X6 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('13',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ X5 @ X6 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','31'])).

thf('36',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('38',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('40',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('50',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('55',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','48','56'])).

thf('58',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','57'])).

thf('59',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','57'])).

thf('66',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('68',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['59','68'])).

thf('70',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['43','58','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','70'])).

thf('72',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','71'])).

thf('73',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','57'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AEuMpYoJR4
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.80/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/1.01  % Solved by: fo/fo7.sh
% 0.80/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.01  % done 1451 iterations in 0.556s
% 0.80/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/1.01  % SZS output start Refutation
% 0.80/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.80/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.80/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.80/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/1.01  thf(t43_zfmisc_1, conjecture,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.80/1.01          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.80/1.01          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.80/1.01          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.80/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.01    (~( ![A:$i,B:$i,C:$i]:
% 0.80/1.01        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.80/1.01             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.80/1.01             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.80/1.01             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.80/1.01    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.80/1.01  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(t2_boole, axiom,
% 0.80/1.01    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.80/1.01  thf('1', plain,
% 0.80/1.01      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.01      inference('cnf', [status(esa)], [t2_boole])).
% 0.80/1.01  thf(t17_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.80/1.01  thf('2', plain,
% 0.80/1.01      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.80/1.01      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.80/1.01  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.80/1.01      inference('sup+', [status(thm)], ['1', '2'])).
% 0.80/1.01  thf(t12_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.80/1.01  thf('4', plain,
% 0.80/1.01      (![X9 : $i, X10 : $i]:
% 0.80/1.01         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.80/1.01      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.80/1.01  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('6', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(t7_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.80/1.01  thf('7', plain,
% 0.80/1.01      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.80/1.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.80/1.01  thf('8', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.80/1.01      inference('sup+', [status(thm)], ['6', '7'])).
% 0.80/1.01  thf(l3_zfmisc_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.80/1.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.80/1.01  thf('9', plain,
% 0.80/1.01      (![X52 : $i, X53 : $i]:
% 0.80/1.01         (((X53) = (k1_tarski @ X52))
% 0.80/1.01          | ((X53) = (k1_xboole_0))
% 0.80/1.01          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.80/1.01      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.80/1.01  thf('10', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.01  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(l98_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( k5_xboole_0 @ A @ B ) =
% 0.80/1.01       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.80/1.01  thf('12', plain,
% 0.80/1.01      (![X5 : $i, X6 : $i]:
% 0.80/1.01         ((k5_xboole_0 @ X5 @ X6)
% 0.80/1.01           = (k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.80/1.01      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.80/1.01  thf('13', plain,
% 0.80/1.01      (((k5_xboole_0 @ sk_B @ sk_C)
% 0.80/1.01         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.80/1.01      inference('sup+', [status(thm)], ['11', '12'])).
% 0.80/1.01  thf('14', plain,
% 0.80/1.01      ((((k5_xboole_0 @ sk_B @ sk_C)
% 0.80/1.01          = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.80/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('sup+', [status(thm)], ['10', '13'])).
% 0.80/1.01  thf(t100_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.80/1.01  thf('15', plain,
% 0.80/1.01      (![X7 : $i, X8 : $i]:
% 0.80/1.01         ((k4_xboole_0 @ X7 @ X8)
% 0.80/1.01           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.80/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.01  thf(t92_xboole_1, axiom,
% 0.80/1.01    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.80/1.01  thf('16', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.80/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.80/1.01  thf(t91_xboole_1, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.80/1.01       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.80/1.01  thf('17', plain,
% 0.80/1.01      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.80/1.01         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.80/1.01           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.80/1.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.80/1.01  thf('18', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]:
% 0.80/1.01         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.80/1.01           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.01      inference('sup+', [status(thm)], ['16', '17'])).
% 0.80/1.01  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('20', plain,
% 0.80/1.01      (![X5 : $i, X6 : $i]:
% 0.80/1.01         ((k5_xboole_0 @ X5 @ X6)
% 0.80/1.01           = (k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.80/1.01      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.80/1.01  thf('21', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.80/1.01           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.80/1.01      inference('sup+', [status(thm)], ['19', '20'])).
% 0.80/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.80/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.80/1.01  thf('22', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.01  thf('23', plain,
% 0.80/1.01      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.01      inference('cnf', [status(esa)], [t2_boole])).
% 0.80/1.01  thf('24', plain,
% 0.80/1.01      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.80/1.01      inference('sup+', [status(thm)], ['22', '23'])).
% 0.80/1.01  thf('25', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.01      inference('demod', [status(thm)], ['21', '24'])).
% 0.80/1.01  thf('26', plain,
% 0.80/1.01      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.01      inference('cnf', [status(esa)], [t2_boole])).
% 0.80/1.01  thf('27', plain,
% 0.80/1.01      (![X7 : $i, X8 : $i]:
% 0.80/1.01         ((k4_xboole_0 @ X7 @ X8)
% 0.80/1.01           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.80/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.01  thf('28', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.01      inference('sup+', [status(thm)], ['26', '27'])).
% 0.80/1.01  thf(t5_boole, axiom,
% 0.80/1.01    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.80/1.01  thf('29', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.80/1.01      inference('cnf', [status(esa)], [t5_boole])).
% 0.80/1.01  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.80/1.01      inference('sup+', [status(thm)], ['28', '29'])).
% 0.80/1.01  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.80/1.01      inference('demod', [status(thm)], ['25', '30'])).
% 0.80/1.01  thf('32', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]:
% 0.80/1.01         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.01      inference('demod', [status(thm)], ['18', '31'])).
% 0.80/1.01  thf('33', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]:
% 0.80/1.01         ((k3_xboole_0 @ X1 @ X0)
% 0.80/1.01           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.80/1.01      inference('sup+', [status(thm)], ['15', '32'])).
% 0.80/1.01  thf('34', plain,
% 0.80/1.01      ((((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.80/1.01          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.80/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('sup+', [status(thm)], ['14', '33'])).
% 0.80/1.01  thf('35', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]:
% 0.80/1.01         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.80/1.01      inference('demod', [status(thm)], ['18', '31'])).
% 0.80/1.01  thf('36', plain,
% 0.80/1.01      ((((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)) = (sk_C))
% 0.80/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('demod', [status(thm)], ['34', '35'])).
% 0.80/1.01  thf('37', plain,
% 0.80/1.01      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.80/1.01      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.80/1.01  thf('38', plain, (((r1_tarski @ sk_C @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('sup+', [status(thm)], ['36', '37'])).
% 0.80/1.01  thf('39', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.01  thf('40', plain,
% 0.80/1.01      (![X52 : $i, X53 : $i]:
% 0.80/1.01         (((X53) = (k1_tarski @ X52))
% 0.80/1.01          | ((X53) = (k1_xboole_0))
% 0.80/1.01          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.80/1.01      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.80/1.01  thf('41', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (~ (r1_tarski @ X0 @ sk_B)
% 0.80/1.01          | ((sk_B) = (k1_xboole_0))
% 0.80/1.01          | ((X0) = (k1_xboole_0))
% 0.80/1.01          | ((X0) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['39', '40'])).
% 0.80/1.01  thf('42', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0))
% 0.80/1.01        | ((sk_C) = (k1_tarski @ sk_A))
% 0.80/1.01        | ((sk_C) = (k1_xboole_0))
% 0.80/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['38', '41'])).
% 0.80/1.01  thf('43', plain,
% 0.80/1.01      ((((sk_C) = (k1_xboole_0))
% 0.80/1.01        | ((sk_C) = (k1_tarski @ sk_A))
% 0.80/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('simplify', [status(thm)], ['42'])).
% 0.80/1.01  thf('44', plain,
% 0.80/1.01      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('45', plain,
% 0.80/1.01      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.80/1.01      inference('split', [status(esa)], ['44'])).
% 0.80/1.01  thf('46', plain,
% 0.80/1.01      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('split', [status(esa)], ['44'])).
% 0.80/1.01  thf('47', plain,
% 0.80/1.01      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('48', plain,
% 0.80/1.01      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('split', [status(esa)], ['47'])).
% 0.80/1.01  thf('49', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.01  thf('50', plain,
% 0.80/1.01      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('51', plain,
% 0.80/1.01      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.80/1.01      inference('split', [status(esa)], ['50'])).
% 0.80/1.01  thf('52', plain,
% 0.80/1.01      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.80/1.01         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['49', '51'])).
% 0.80/1.01  thf('53', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.80/1.01      inference('simplify', [status(thm)], ['52'])).
% 0.80/1.01  thf('54', plain,
% 0.80/1.01      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.80/1.01      inference('split', [status(esa)], ['44'])).
% 0.80/1.01  thf('55', plain,
% 0.80/1.01      ((((sk_B) != (sk_B)))
% 0.80/1.01         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['53', '54'])).
% 0.80/1.01  thf('56', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('simplify', [status(thm)], ['55'])).
% 0.80/1.01  thf('57', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('sat_resolution*', [status(thm)], ['46', '48', '56'])).
% 0.80/1.01  thf('58', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.80/1.01      inference('simpl_trail', [status(thm)], ['45', '57'])).
% 0.80/1.01  thf('59', plain,
% 0.80/1.01      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.80/1.01      inference('split', [status(esa)], ['50'])).
% 0.80/1.01  thf('60', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('61', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.80/1.01      inference('simplify', [status(thm)], ['52'])).
% 0.80/1.01  thf('62', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('63', plain,
% 0.80/1.01      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.80/1.01         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.80/1.01      inference('sup+', [status(thm)], ['61', '62'])).
% 0.80/1.01  thf('64', plain,
% 0.80/1.01      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.80/1.01      inference('sup+', [status(thm)], ['60', '63'])).
% 0.80/1.01  thf('65', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.80/1.01      inference('simpl_trail', [status(thm)], ['45', '57'])).
% 0.80/1.01  thf('66', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.80/1.01  thf('67', plain,
% 0.80/1.01      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.80/1.01      inference('split', [status(esa)], ['50'])).
% 0.80/1.01  thf('68', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.80/1.01      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.80/1.01  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 0.80/1.01      inference('simpl_trail', [status(thm)], ['59', '68'])).
% 0.80/1.01  thf('70', plain, (((sk_B) = (k1_xboole_0))),
% 0.80/1.01      inference('simplify_reflect-', [status(thm)], ['43', '58', '69'])).
% 0.80/1.01  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.80/1.01      inference('demod', [status(thm)], ['5', '70'])).
% 0.80/1.01  thf('72', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.80/1.01      inference('demod', [status(thm)], ['0', '71'])).
% 0.80/1.01  thf('73', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.80/1.01      inference('simpl_trail', [status(thm)], ['45', '57'])).
% 0.80/1.01  thf('74', plain, ($false),
% 0.80/1.01      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.80/1.01  
% 0.80/1.01  % SZS output end Refutation
% 0.80/1.01  
% 0.80/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
