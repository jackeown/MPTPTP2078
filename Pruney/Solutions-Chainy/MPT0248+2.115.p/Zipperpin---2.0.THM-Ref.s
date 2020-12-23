%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LrBHOW1Fcu

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:34 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 281 expanded)
%              Number of leaves         :   24 (  85 expanded)
%              Depth                    :   22
%              Number of atoms          :  812 (2997 expanded)
%              Number of equality atoms :  119 ( 543 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X7 @ X5 ) ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ ( k2_tarski @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('18',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('23',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) ) )
      = X27 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['21','24'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('40',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','19','41'])).

thf('43',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['16','42'])).

thf('44',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('47',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k1_tarski @ X50 ) )
      | ( X49 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('50',plain,(
    ! [X50: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X50 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('54',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( X36 = X33 )
      | ( X35
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('55',plain,(
    ! [X33: $i,X36: $i] :
      ( ( X36 = X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('64',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('65',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('66',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X26 @ X25 ) )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_B_1 )
        | ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) )
          = X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = sk_C_2 )
      | ( sk_C_2 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','67'])).

thf('69',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['16','42'])).

thf('70',plain,
    ( ( sk_C_2 = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('72',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('73',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('74',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('75',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X26 @ X25 ) )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','80'])).

thf('82',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','81'])).

thf('83',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('84',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('86',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['44','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','43','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LrBHOW1Fcu
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:49:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.58/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.76  % Solved by: fo/fo7.sh
% 0.58/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.76  % done 494 iterations in 0.283s
% 0.58/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.76  % SZS output start Refutation
% 0.58/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.76  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.58/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.76  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.76  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.76  thf(t43_zfmisc_1, conjecture,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.58/0.76          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.58/0.76          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.58/0.76          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.76        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.58/0.76             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.58/0.76             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.58/0.76             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.58/0.76  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(l51_zfmisc_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.76  thf('1', plain,
% 0.58/0.76      (![X51 : $i, X52 : $i]:
% 0.58/0.76         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.58/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.76  thf(d3_tarski, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.76  thf('3', plain,
% 0.58/0.76      (![X1 : $i, X3 : $i]:
% 0.58/0.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf(d3_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.58/0.76       ( ![D:$i]:
% 0.58/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.76           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.58/0.76  thf('4', plain,
% 0.58/0.76      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X4 @ X5)
% 0.58/0.76          | (r2_hidden @ X4 @ X6)
% 0.58/0.76          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.58/0.76         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.58/0.76      inference('simplify', [status(thm)], ['4'])).
% 0.58/0.76  thf('6', plain,
% 0.58/0.76      (![X51 : $i, X52 : $i]:
% 0.58/0.76         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.58/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.76  thf('7', plain,
% 0.58/0.76      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.58/0.76         ((r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X7 @ X5)))
% 0.58/0.76          | ~ (r2_hidden @ X4 @ X5))),
% 0.58/0.76      inference('demod', [status(thm)], ['5', '6'])).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((r1_tarski @ X0 @ X1)
% 0.58/0.76          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ (k2_tarski @ X2 @ X0))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['3', '7'])).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      (![X1 : $i, X3 : $i]:
% 0.58/0.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 0.58/0.76          | (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.76  thf('11', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['10'])).
% 0.58/0.76  thf('12', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.58/0.76      inference('sup+', [status(thm)], ['2', '11'])).
% 0.58/0.76  thf(l3_zfmisc_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.58/0.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X48 : $i, X49 : $i]:
% 0.58/0.76         (((X49) = (k1_tarski @ X48))
% 0.58/0.76          | ((X49) = (k1_xboole_0))
% 0.58/0.76          | ~ (r1_tarski @ X49 @ (k1_tarski @ X48)))),
% 0.58/0.76      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.58/0.76  thf('14', plain,
% 0.58/0.76      ((((sk_C_2) = (k1_xboole_0)) | ((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('15', plain,
% 0.58/0.76      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.58/0.76         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('split', [status(esa)], ['15'])).
% 0.58/0.76  thf('17', plain,
% 0.58/0.76      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.58/0.76      inference('split', [status(esa)], ['15'])).
% 0.58/0.76  thf('18', plain,
% 0.58/0.76      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('19', plain,
% 0.58/0.76      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.58/0.76       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('split', [status(esa)], ['18'])).
% 0.58/0.76  thf('20', plain,
% 0.58/0.76      (![X1 : $i, X3 : $i]:
% 0.58/0.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf('21', plain,
% 0.58/0.76      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.76  thf(t21_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.58/0.76  thf('22', plain,
% 0.58/0.76      (![X27 : $i, X28 : $i]:
% 0.58/0.76         ((k3_xboole_0 @ X27 @ (k2_xboole_0 @ X27 @ X28)) = (X27))),
% 0.58/0.76      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.58/0.76  thf('23', plain,
% 0.58/0.76      (![X51 : $i, X52 : $i]:
% 0.58/0.76         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.58/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.76  thf('24', plain,
% 0.58/0.76      (![X27 : $i, X28 : $i]:
% 0.58/0.76         ((k3_xboole_0 @ X27 @ (k3_tarski @ (k2_tarski @ X27 @ X28))) = (X27))),
% 0.58/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.58/0.76  thf('25', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['21', '24'])).
% 0.58/0.76  thf(d4_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.58/0.76       ( ![D:$i]:
% 0.58/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.76           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X14 @ X13)
% 0.58/0.76          | (r2_hidden @ X14 @ X12)
% 0.58/0.76          | ((X13) != (k3_xboole_0 @ X11 @ X12)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.58/0.76         ((r2_hidden @ X14 @ X12)
% 0.58/0.76          | ~ (r2_hidden @ X14 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['26'])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X0 @ sk_B_1) | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['25', '27'])).
% 0.58/0.76  thf('29', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((r1_tarski @ sk_B_1 @ X0)
% 0.58/0.76          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['20', '28'])).
% 0.58/0.76  thf('30', plain,
% 0.58/0.76      (![X1 : $i, X3 : $i]:
% 0.58/0.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf('31', plain,
% 0.58/0.76      (((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.58/0.76        | (r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.76  thf('32', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.58/0.76      inference('simplify', [status(thm)], ['31'])).
% 0.58/0.76  thf('33', plain,
% 0.58/0.76      (![X48 : $i, X49 : $i]:
% 0.58/0.76         (((X49) = (k1_tarski @ X48))
% 0.58/0.76          | ((X49) = (k1_xboole_0))
% 0.58/0.76          | ~ (r1_tarski @ X49 @ (k1_tarski @ X48)))),
% 0.58/0.76      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.58/0.76  thf('34', plain,
% 0.58/0.76      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('split', [status(esa)], ['35'])).
% 0.58/0.76  thf('37', plain,
% 0.58/0.76      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['34', '36'])).
% 0.58/0.76  thf('38', plain,
% 0.58/0.76      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('simplify', [status(thm)], ['37'])).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.76      inference('split', [status(esa)], ['15'])).
% 0.58/0.76  thf('40', plain,
% 0.58/0.76      ((((sk_B_1) != (sk_B_1)))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.58/0.76             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.76  thf('41', plain,
% 0.58/0.76      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.76  thf('42', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('sat_resolution*', [status(thm)], ['17', '19', '41'])).
% 0.58/0.76  thf('43', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.58/0.76      inference('simpl_trail', [status(thm)], ['16', '42'])).
% 0.58/0.76  thf('44', plain,
% 0.58/0.76      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.58/0.76      inference('split', [status(esa)], ['35'])).
% 0.58/0.76  thf('45', plain,
% 0.58/0.76      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.76  thf('46', plain,
% 0.58/0.76      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('simplify', [status(thm)], ['37'])).
% 0.58/0.76  thf(t7_xboole_0, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.76          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.76  thf('47', plain,
% 0.58/0.76      (![X22 : $i]:
% 0.58/0.76         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.58/0.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.76  thf('48', plain,
% 0.58/0.76      (![X1 : $i, X3 : $i]:
% 0.58/0.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf('49', plain,
% 0.58/0.76      (![X49 : $i, X50 : $i]:
% 0.58/0.76         ((r1_tarski @ X49 @ (k1_tarski @ X50)) | ((X49) != (k1_xboole_0)))),
% 0.58/0.76      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.58/0.76  thf('50', plain,
% 0.58/0.76      (![X50 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X50))),
% 0.58/0.76      inference('simplify', [status(thm)], ['49'])).
% 0.58/0.76  thf('51', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.76          | (r2_hidden @ X0 @ X2)
% 0.58/0.76          | ~ (r1_tarski @ X1 @ X2))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf('52', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.58/0.76          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.76  thf('53', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.58/0.76          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k1_tarski @ X1)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['48', '52'])).
% 0.58/0.76  thf(d1_tarski, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.58/0.76  thf('54', plain,
% 0.58/0.76      (![X33 : $i, X35 : $i, X36 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X36 @ X35)
% 0.58/0.76          | ((X36) = (X33))
% 0.58/0.76          | ((X35) != (k1_tarski @ X33)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.76  thf('55', plain,
% 0.58/0.76      (![X33 : $i, X36 : $i]:
% 0.58/0.76         (((X36) = (X33)) | ~ (r2_hidden @ X36 @ (k1_tarski @ X33)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['54'])).
% 0.58/0.76  thf('56', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['53', '55'])).
% 0.58/0.76  thf('57', plain,
% 0.58/0.76      (![X1 : $i, X3 : $i]:
% 0.58/0.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf('58', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.76          | (r1_tarski @ k1_xboole_0 @ X1)
% 0.58/0.76          | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.76  thf('59', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r1_tarski @ k1_xboole_0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.76      inference('simplify', [status(thm)], ['58'])).
% 0.58/0.76  thf('60', plain,
% 0.58/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['47', '59'])).
% 0.58/0.76  thf('61', plain,
% 0.58/0.76      ((![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ((X0) = (k1_xboole_0))))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('sup+', [status(thm)], ['46', '60'])).
% 0.58/0.76  thf('62', plain,
% 0.58/0.76      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('simplify', [status(thm)], ['37'])).
% 0.58/0.76  thf('63', plain,
% 0.58/0.76      ((![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ((X0) = (sk_B_1))))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('demod', [status(thm)], ['61', '62'])).
% 0.58/0.76  thf(t12_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.58/0.76  thf('64', plain,
% 0.58/0.76      (![X25 : $i, X26 : $i]:
% 0.58/0.76         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.58/0.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.76  thf('65', plain,
% 0.58/0.76      (![X51 : $i, X52 : $i]:
% 0.58/0.76         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.58/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.76  thf('66', plain,
% 0.58/0.76      (![X25 : $i, X26 : $i]:
% 0.58/0.76         (((k3_tarski @ (k2_tarski @ X26 @ X25)) = (X25))
% 0.58/0.76          | ~ (r1_tarski @ X26 @ X25))),
% 0.58/0.76      inference('demod', [status(thm)], ['64', '65'])).
% 0.58/0.76  thf('67', plain,
% 0.58/0.76      ((![X0 : $i]:
% 0.58/0.76          (((X0) = (sk_B_1)) | ((k3_tarski @ (k2_tarski @ sk_B_1 @ X0)) = (X0))))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['63', '66'])).
% 0.58/0.76  thf('68', plain,
% 0.58/0.76      (((((k1_tarski @ sk_A) = (sk_C_2)) | ((sk_C_2) = (sk_B_1))))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('sup+', [status(thm)], ['45', '67'])).
% 0.58/0.76  thf('69', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.58/0.76      inference('simpl_trail', [status(thm)], ['16', '42'])).
% 0.58/0.76  thf('70', plain,
% 0.58/0.76      ((((sk_C_2) = (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.58/0.76  thf('71', plain,
% 0.58/0.76      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.76  thf('72', plain,
% 0.58/0.76      ((((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_B_1))))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.76  thf(t69_enumset1, axiom,
% 0.58/0.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.76  thf('73', plain,
% 0.58/0.76      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.58/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.76  thf('74', plain,
% 0.58/0.76      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.58/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.76  thf('75', plain,
% 0.58/0.76      (![X1 : $i, X3 : $i]:
% 0.58/0.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf('76', plain,
% 0.58/0.76      (![X1 : $i, X3 : $i]:
% 0.58/0.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.76  thf('77', plain,
% 0.58/0.76      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['75', '76'])).
% 0.58/0.76  thf('78', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.58/0.76      inference('simplify', [status(thm)], ['77'])).
% 0.58/0.76  thf('79', plain,
% 0.58/0.76      (![X25 : $i, X26 : $i]:
% 0.58/0.76         (((k3_tarski @ (k2_tarski @ X26 @ X25)) = (X25))
% 0.58/0.76          | ~ (r1_tarski @ X26 @ X25))),
% 0.58/0.76      inference('demod', [status(thm)], ['64', '65'])).
% 0.58/0.76  thf('80', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.76  thf('81', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['74', '80'])).
% 0.58/0.76  thf('82', plain,
% 0.58/0.76      ((((k1_tarski @ sk_A) = (sk_B_1)))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('demod', [status(thm)], ['72', '73', '81'])).
% 0.58/0.76  thf('83', plain,
% 0.58/0.76      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.58/0.76         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.76      inference('split', [status(esa)], ['35'])).
% 0.58/0.76  thf('84', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 0.58/0.76  thf('85', plain,
% 0.58/0.76      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('split', [status(esa)], ['35'])).
% 0.58/0.76  thf('86', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.58/0.76      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.58/0.76  thf('87', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.58/0.76      inference('simpl_trail', [status(thm)], ['44', '86'])).
% 0.58/0.76  thf('88', plain, ($false),
% 0.58/0.76      inference('simplify_reflect-', [status(thm)], ['14', '43', '87'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.58/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
