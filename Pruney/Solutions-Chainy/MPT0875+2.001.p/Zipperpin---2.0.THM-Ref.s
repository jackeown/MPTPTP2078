%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JTz2TVW25C

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 358 expanded)
%              Number of leaves         :    9 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  763 (4147 expanded)
%              Number of equality atoms :  184 (1046 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t35_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) )
      <=> ( ( k3_zfmisc_1 @ A @ B @ C )
         != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t35_mcart_1])).

thf('0',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_C )
        = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_C )
        = sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_C )
        = sk_C )
   <= ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
       != k1_xboole_0 )
      & ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_C != sk_C )
   <= ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
       != k1_xboole_0 )
      & ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('19',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( sk_C != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_C != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('34',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('37',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_C != k1_xboole_0 )
      & ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','51'])).

thf('53',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','17','18','20','38','57','58'])).

thf('60',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('61',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','17','18','20','38','57','58'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
      = sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','72'])).

thf('74',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','17','18','20','38'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JTz2TVW25C
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 171 iterations in 0.044s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(t35_mcart_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.52       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52            ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.52          ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t35_mcart_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.20/0.52        | ((sk_C) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0))
% 0.20/0.52        | ((sk_C) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (~ (((sk_C) = (k1_xboole_0))) | 
% 0.20/0.52       ~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf(d3_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.52       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.20/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.52  thf('5', plain, ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf(t113_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_C) = (k1_xboole_0)))
% 0.20/0.52         <= ((((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '7'])).
% 0.20/0.52  thf('9', plain, ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_C) = (sk_C)))
% 0.20/0.52         <= ((((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ X1 @ X0 @ sk_C) = (sk_C)))
% 0.20/0.52         <= ((((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['4', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0))
% 0.20/0.52        | ((sk_A) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((((sk_C) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             (((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((((sk_C) = (k1_xboole_0))) <= ((((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((((sk_C) != (sk_C)))
% 0.20/0.52         <= (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             (((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (~ (((sk_C) = (k1_xboole_0))) | 
% 0.20/0.52       (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))) | 
% 0.20/0.52       ~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('split', [status(esa)], ['12'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0))
% 0.20/0.52        | ((sk_B) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.20/0.52       ~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('split', [status(esa)], ['19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))
% 0.20/0.52         <= ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.20/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.52          | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52         | ((sk_C) = (k1_xboole_0))
% 0.20/0.52         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.20/0.52         <= ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.52         <= ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52         | ((sk_C) = (k1_xboole_0))
% 0.20/0.52         | ((sk_A) = (k1_xboole_0))
% 0.20/0.52         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.52         <= ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((((sk_B) = (k1_xboole_0))
% 0.20/0.52         | ((sk_A) = (k1_xboole_0))
% 0.20/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.52         <= ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((((sk_C) != (sk_C))
% 0.20/0.52         | ((sk_A) = (k1_xboole_0))
% 0.20/0.52         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.52         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.52         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['19'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.52         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.20/0.52             (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.52         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.20/0.52             (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['12'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((((sk_A) != (sk_A)))
% 0.20/0.52         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             ~ (((sk_B) = (k1_xboole_0))) & 
% 0.20/0.52             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.20/0.52             (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((((sk_A) = (k1_xboole_0))) | 
% 0.20/0.52       ~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))) | 
% 0.20/0.52       (((sk_B) = (k1_xboole_0))) | (((sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0)))
% 0.20/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ X0 @ sk_B) = (sk_B)))
% 0.20/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.20/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((![X0 : $i, X1 : $i]:
% 0.20/0.52          ((k3_zfmisc_1 @ X1 @ sk_B @ X0) = (k2_zfmisc_1 @ sk_B @ X0)))
% 0.20/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0)))
% 0.20/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['46', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_B @ X0) = (sk_B)))
% 0.20/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      ((![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ X1 @ sk_B @ X0) = (sk_B)))
% 0.20/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['45', '51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['12'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      ((((sk_B) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             (((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      ((((sk_B) != (sk_B)))
% 0.20/0.52         <= (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))) & 
% 0.20/0.52             (((sk_B) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.20/0.52       (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      ((((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0))) | 
% 0.20/0.52       (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))) | 
% 0.20/0.52       (((sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('59', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)],
% 0.20/0.52                ['3', '17', '18', '20', '38', '57', '58'])).
% 0.20/0.52  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['12'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 0.20/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.20/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.20/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      ((![X0 : $i, X1 : $i]:
% 0.20/0.52          ((k3_zfmisc_1 @ sk_A @ X1 @ X0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['66', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.20/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      ((![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ sk_A @ X1 @ X0) = (sk_A)))
% 0.20/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.52  thf('71', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)],
% 0.20/0.52                ['3', '17', '18', '20', '38', '57', '58'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ sk_A @ X1 @ X0) = (sk_A))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      ((((sk_A) != (k1_xboole_0)))
% 0.20/0.52         <= (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))))),
% 0.20/0.52      inference('demod', [status(thm)], ['61', '72'])).
% 0.20/0.52  thf('74', plain, (~ (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['3', '17', '18', '20', '38'])).
% 0.20/0.52  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['73', '74'])).
% 0.20/0.52  thf('76', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['60', '75'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
