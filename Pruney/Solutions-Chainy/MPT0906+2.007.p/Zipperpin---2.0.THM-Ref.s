%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YDB1E6fyNw

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 389 expanded)
%              Number of leaves         :   19 ( 139 expanded)
%              Depth                    :   19
%              Number of atoms          :  743 (4257 expanded)
%              Number of equality atoms :  119 ( 488 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t66_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
       != k1_xboole_0 )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
         => ( ( C
             != ( k1_mcart_1 @ C ) )
            & ( C
             != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
         != k1_xboole_0 )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
           => ( ( C
               != ( k1_mcart_1 @ C ) )
              & ( C
               != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_mcart_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t122_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X38 @ X40 ) @ X39 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('14',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ ( k3_xboole_0 @ X34 @ X36 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X34 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ ( k3_xboole_0 @ X34 @ X36 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X34 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X38: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ X41 @ ( k4_xboole_0 @ X38 @ X40 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X38 ) @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('28',plain,(
    ! [X38: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ X41 @ ( k4_xboole_0 @ X38 @ X40 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X38 ) @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','33','34'])).

thf('36',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('39',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45
       != ( k1_mcart_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k2_zfmisc_1 @ X44 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
     != ( k1_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','33','34'])).

thf('48',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['36'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45
       != ( k2_mcart_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k2_zfmisc_1 @ X44 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
     != ( k2_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    sk_C
 != ( k2_mcart_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['36'])).

thf('66',plain,
    ( sk_C
    = ( k1_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['46','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('69',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','67','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YDB1E6fyNw
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 135 iterations in 0.076s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(t66_mcart_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.54           ( ( ( C ) != ( k1_mcart_1 @ C ) ) & ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.54          ( ![C:$i]:
% 0.20/0.54            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.54              ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.54                ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t66_mcart_1])).
% 0.20/0.54  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t92_xboole_1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('1', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.54  thf(t21_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.54  thf(t122_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.54         ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.20/0.54       ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.54         ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k3_xboole_0 @ X34 @ X36) @ X35)
% 0.20/0.54           = (k3_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 0.20/0.54  thf(t100_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.20/0.54              (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ 
% 0.20/0.54           (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ X2) @ X1))
% 0.20/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['2', '5'])).
% 0.20/0.54  thf('7', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ 
% 0.20/0.54           (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ X2) @ X1)) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf(t125_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.20/0.54         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.20/0.54       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.54         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ X38 @ X40) @ X39)
% 0.20/0.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X40 @ X39)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.20/0.54           = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ X37 @ (k3_xboole_0 @ X34 @ X36))
% 0.20/0.54           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X34) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X37 @ X36)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 0.20/0.54           = (k3_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.54              (k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ X37 @ (k3_xboole_0 @ X34 @ X36))
% 0.20/0.54           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X34) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X37 @ X36)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X2 @ X0))
% 0.20/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X38 : $i, X40 : $i, X41 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ X41 @ (k4_xboole_0 @ X38 @ X40))
% 0.20/0.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X41 @ X38) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X41 @ X40)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ X1 @ 
% 0.20/0.54           (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)))
% 0.20/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X1 @ k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['19', '24'])).
% 0.20/0.54  thf('26', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X38 : $i, X40 : $i, X41 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ X41 @ (k4_xboole_0 @ X38 @ X40))
% 0.20/0.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X41 @ X38) @ 
% 0.20/0.54              (k2_zfmisc_1 @ X41 @ X40)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 0.20/0.54           = (k4_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.54              (k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['26', '32'])).
% 0.20/0.54  thf('34', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '33', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('split', [status(esa)], ['36'])).
% 0.20/0.54  thf('38', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t26_mcart_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.54          ( ~( ![C:$i]:
% 0.20/0.54               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.54                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.54                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.54         (((X44) = (k1_xboole_0))
% 0.20/0.54          | ((X45) != (k1_mcart_1 @ X45))
% 0.20/0.54          | ~ (m1_subset_1 @ X45 @ (k2_zfmisc_1 @ X44 @ X46))
% 0.20/0.54          | ((X46) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_C) != (k1_mcart_1 @ sk_C))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((((sk_C) != (sk_C))
% 0.20/0.54         | ((sk_A) = (k1_xboole_0))
% 0.20/0.54         | ((sk_B) = (k1_xboole_0)))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['37', '40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.54         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.54  thf('43', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54         | ((sk_A) = (k1_xboole_0)))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.54         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '33', '34'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('split', [status(esa)], ['36'])).
% 0.20/0.54  thf('49', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.54         (((X44) = (k1_xboole_0))
% 0.20/0.54          | ((X45) != (k2_mcart_1 @ X45))
% 0.20/0.54          | ~ (m1_subset_1 @ X45 @ (k2_zfmisc_1 @ X44 @ X46))
% 0.20/0.54          | ((X46) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_C) != (k2_mcart_1 @ sk_C))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (((((sk_C) != (sk_C))
% 0.20/0.54         | ((sk_A) = (k1_xboole_0))
% 0.20/0.54         | ((sk_B) = (k1_xboole_0)))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.54         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.54  thf('54', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54         | ((sk_A) = (k1_xboole_0)))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.54         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['47', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.54  thf('58', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.20/0.54         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '62'])).
% 0.20/0.54  thf('64', plain, (~ (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((((sk_C) = (k1_mcart_1 @ sk_C))) | (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.54      inference('split', [status(esa)], ['36'])).
% 0.20/0.54  thf('66', plain, ((((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.20/0.54  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['46', '66'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('69', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '67', '68'])).
% 0.20/0.54  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
