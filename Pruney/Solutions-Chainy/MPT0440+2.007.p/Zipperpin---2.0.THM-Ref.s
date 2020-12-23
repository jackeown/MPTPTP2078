%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjiraRAZoD

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:42 EST 2020

% Result     : Theorem 7.83s
% Output     : Refutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  125 (1175 expanded)
%              Number of leaves         :   27 ( 353 expanded)
%              Depth                    :   28
%              Number of atoms          :  990 (10740 expanded)
%              Number of equality atoms :   69 ( 932 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('0',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X45 @ X46 )
      | ~ ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['1','7'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('9',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X49 @ X50 ) @ X51 )
      | ( r2_hidden @ X49 @ X52 )
      | ( X52
       != ( k1_relat_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('10',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ X49 @ ( k1_relat_1 @ X51 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X49 @ X50 ) @ X51 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('13',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( r2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( r2_hidden @ ( sk_C @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_A ) ) @ ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X53 @ X52 )
      | ( r2_hidden @ ( k4_tarski @ X53 @ ( sk_D_1 @ X53 @ X51 ) ) @ X51 )
      | ( X52
       != ( k1_relat_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('23',plain,(
    ! [X51: $i,X53: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X53 @ ( sk_D_1 @ X53 @ X51 ) ) @ X51 )
      | ~ ( r2_hidden @ X53 @ ( k1_relat_1 @ X51 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_A ) ) @ ( sk_D_1 @ ( sk_C @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_A ) ) @ sk_C_3 ) ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('27',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_tarski @ ( k4_tarski @ X41 @ X42 ) @ ( k4_tarski @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('31',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ ( k2_zfmisc_1 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_3 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( r2_hidden @ ( sk_C @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ~ ( r2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( r2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_C_3
    = ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','40'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('42',plain,(
    ! [X58: $i,X61: $i] :
      ( ( X61
        = ( k2_relat_1 @ X58 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X61 @ X58 ) @ ( sk_C_2 @ X61 @ X58 ) ) @ X58 )
      | ( r2_hidden @ ( sk_C_2 @ X61 @ X58 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('43',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ~ ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ ( k2_zfmisc_1 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['44'])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['41','45'])).

thf('47',plain,
    ( sk_C_3
    = ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','40'])).

thf('48',plain,
    ( ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('52',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['49'])).

thf('53',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['49'])).

thf('56',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['50','56'])).

thf('58',plain,(
    r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('60',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ sk_B ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('64',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X47 @ X46 )
      | ~ ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('67',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_tarski @ sk_B @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('85',plain,(
    ! [X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ ( k2_zfmisc_1 @ X37 @ X40 ) )
      | ~ ( r2_hidden @ X38 @ X40 )
      | ~ ( r2_hidden @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,
    ( sk_C_3
    = ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','40'])).

thf('90',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) ) @ sk_C_3 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X58: $i,X61: $i,X62: $i] :
      ( ( X61
        = ( k2_relat_1 @ X58 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X62 @ ( sk_C_2 @ X61 @ X58 ) ) @ X58 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X61 @ X58 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('92',plain,
    ( ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['48','57'])).

thf('94',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['50','56'])).

thf('96',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjiraRAZoD
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.83/8.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.83/8.02  % Solved by: fo/fo7.sh
% 7.83/8.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.83/8.02  % done 6907 iterations in 7.526s
% 7.83/8.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.83/8.02  % SZS output start Refutation
% 7.83/8.02  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 7.83/8.02  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.83/8.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.83/8.02  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 7.83/8.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.83/8.02  thf(sk_A_type, type, sk_A: $i).
% 7.83/8.02  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 7.83/8.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.83/8.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.83/8.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.83/8.02  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 7.83/8.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.83/8.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.83/8.02  thf(sk_C_3_type, type, sk_C_3: $i).
% 7.83/8.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.83/8.02  thf(sk_B_type, type, sk_B: $i).
% 7.83/8.02  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 7.83/8.02  thf(t23_relat_1, conjecture,
% 7.83/8.02    (![A:$i,B:$i,C:$i]:
% 7.83/8.02     ( ( v1_relat_1 @ C ) =>
% 7.83/8.02       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 7.83/8.02         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 7.83/8.02           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 7.83/8.02  thf(zf_stmt_0, negated_conjecture,
% 7.83/8.02    (~( ![A:$i,B:$i,C:$i]:
% 7.83/8.02        ( ( v1_relat_1 @ C ) =>
% 7.83/8.02          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 7.83/8.02            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 7.83/8.02              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 7.83/8.02    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 7.83/8.02  thf('0', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 7.83/8.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.83/8.02  thf('1', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 7.83/8.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.83/8.02  thf(t69_enumset1, axiom,
% 7.83/8.02    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 7.83/8.02  thf('2', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 7.83/8.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.83/8.02  thf(d10_xboole_0, axiom,
% 7.83/8.02    (![A:$i,B:$i]:
% 7.83/8.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.83/8.02  thf('3', plain,
% 7.83/8.02      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 7.83/8.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.83/8.02  thf('4', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 7.83/8.02      inference('simplify', [status(thm)], ['3'])).
% 7.83/8.02  thf(t38_zfmisc_1, axiom,
% 7.83/8.02    (![A:$i,B:$i,C:$i]:
% 7.83/8.02     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 7.83/8.02       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 7.83/8.02  thf('5', plain,
% 7.83/8.02      (![X45 : $i, X46 : $i, X47 : $i]:
% 7.83/8.02         ((r2_hidden @ X45 @ X46)
% 7.83/8.02          | ~ (r1_tarski @ (k2_tarski @ X45 @ X47) @ X46))),
% 7.83/8.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 7.83/8.02  thf('6', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['4', '5'])).
% 7.83/8.02  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.83/8.02      inference('sup+', [status(thm)], ['2', '6'])).
% 7.83/8.02  thf('8', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 7.83/8.02      inference('sup+', [status(thm)], ['1', '7'])).
% 7.83/8.02  thf(d4_relat_1, axiom,
% 7.83/8.02    (![A:$i,B:$i]:
% 7.83/8.02     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 7.83/8.02       ( ![C:$i]:
% 7.83/8.02         ( ( r2_hidden @ C @ B ) <=>
% 7.83/8.02           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 7.83/8.02  thf('9', plain,
% 7.83/8.02      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 7.83/8.02         (~ (r2_hidden @ (k4_tarski @ X49 @ X50) @ X51)
% 7.83/8.02          | (r2_hidden @ X49 @ X52)
% 7.83/8.02          | ((X52) != (k1_relat_1 @ X51)))),
% 7.83/8.02      inference('cnf', [status(esa)], [d4_relat_1])).
% 7.83/8.02  thf('10', plain,
% 7.83/8.02      (![X49 : $i, X50 : $i, X51 : $i]:
% 7.83/8.02         ((r2_hidden @ X49 @ (k1_relat_1 @ X51))
% 7.83/8.02          | ~ (r2_hidden @ (k4_tarski @ X49 @ X50) @ X51))),
% 7.83/8.02      inference('simplify', [status(thm)], ['9'])).
% 7.83/8.02  thf('11', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 7.83/8.02      inference('sup-', [status(thm)], ['8', '10'])).
% 7.83/8.02  thf('12', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 7.83/8.02      inference('sup-', [status(thm)], ['8', '10'])).
% 7.83/8.02  thf('13', plain,
% 7.83/8.02      (![X45 : $i, X47 : $i, X48 : $i]:
% 7.83/8.02         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 7.83/8.02          | ~ (r2_hidden @ X47 @ X48)
% 7.83/8.02          | ~ (r2_hidden @ X45 @ X48))),
% 7.83/8.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 7.83/8.02  thf('14', plain,
% 7.83/8.02      (![X0 : $i]:
% 7.83/8.02         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3))
% 7.83/8.02          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ (k1_relat_1 @ sk_C_3)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['12', '13'])).
% 7.83/8.02  thf('15', plain,
% 7.83/8.02      ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ (k1_relat_1 @ sk_C_3))),
% 7.83/8.02      inference('sup-', [status(thm)], ['11', '14'])).
% 7.83/8.02  thf('16', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 7.83/8.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.83/8.02  thf('17', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_3))),
% 7.83/8.02      inference('demod', [status(thm)], ['15', '16'])).
% 7.83/8.02  thf(d8_xboole_0, axiom,
% 7.83/8.02    (![A:$i,B:$i]:
% 7.83/8.02     ( ( r2_xboole_0 @ A @ B ) <=>
% 7.83/8.02       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 7.83/8.02  thf('18', plain,
% 7.83/8.02      (![X0 : $i, X2 : $i]:
% 7.83/8.02         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 7.83/8.02      inference('cnf', [status(esa)], [d8_xboole_0])).
% 7.83/8.02  thf('19', plain,
% 7.83/8.02      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.83/8.02        | (r2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_3)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['17', '18'])).
% 7.83/8.02  thf(t6_xboole_0, axiom,
% 7.83/8.02    (![A:$i,B:$i]:
% 7.83/8.02     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 7.83/8.02          ( ![C:$i]:
% 7.83/8.02            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 7.83/8.02  thf('20', plain,
% 7.83/8.02      (![X3 : $i, X4 : $i]:
% 7.83/8.02         (~ (r2_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 7.83/8.02      inference('cnf', [status(esa)], [t6_xboole_0])).
% 7.83/8.02  thf('21', plain,
% 7.83/8.02      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.83/8.02        | (r2_hidden @ (sk_C @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_A)) @ 
% 7.83/8.02           (k1_relat_1 @ sk_C_3)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['19', '20'])).
% 7.83/8.02  thf('22', plain,
% 7.83/8.02      (![X51 : $i, X52 : $i, X53 : $i]:
% 7.83/8.02         (~ (r2_hidden @ X53 @ X52)
% 7.83/8.02          | (r2_hidden @ (k4_tarski @ X53 @ (sk_D_1 @ X53 @ X51)) @ X51)
% 7.83/8.02          | ((X52) != (k1_relat_1 @ X51)))),
% 7.83/8.02      inference('cnf', [status(esa)], [d4_relat_1])).
% 7.83/8.02  thf('23', plain,
% 7.83/8.02      (![X51 : $i, X53 : $i]:
% 7.83/8.02         ((r2_hidden @ (k4_tarski @ X53 @ (sk_D_1 @ X53 @ X51)) @ X51)
% 7.83/8.02          | ~ (r2_hidden @ X53 @ (k1_relat_1 @ X51)))),
% 7.83/8.02      inference('simplify', [status(thm)], ['22'])).
% 7.83/8.02  thf('24', plain,
% 7.83/8.02      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.83/8.02        | (r2_hidden @ 
% 7.83/8.02           (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_A)) @ 
% 7.83/8.02            (sk_D_1 @ (sk_C @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_A)) @ 
% 7.83/8.02             sk_C_3)) @ 
% 7.83/8.02           sk_C_3))),
% 7.83/8.02      inference('sup-', [status(thm)], ['21', '23'])).
% 7.83/8.02  thf('25', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 7.83/8.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.83/8.02  thf('26', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 7.83/8.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.83/8.02  thf(t36_zfmisc_1, axiom,
% 7.83/8.02    (![A:$i,B:$i,C:$i]:
% 7.83/8.02     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 7.83/8.02         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 7.83/8.02       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 7.83/8.02         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 7.83/8.02  thf('27', plain,
% 7.83/8.02      (![X41 : $i, X42 : $i, X43 : $i]:
% 7.83/8.02         ((k2_zfmisc_1 @ (k1_tarski @ X41) @ (k2_tarski @ X42 @ X43))
% 7.83/8.02           = (k2_tarski @ (k4_tarski @ X41 @ X42) @ (k4_tarski @ X41 @ X43)))),
% 7.83/8.02      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 7.83/8.02  thf('28', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 7.83/8.02           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 7.83/8.02      inference('sup+', [status(thm)], ['26', '27'])).
% 7.83/8.02  thf('29', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 7.83/8.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.83/8.02  thf('30', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 7.83/8.02           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 7.83/8.02      inference('demod', [status(thm)], ['28', '29'])).
% 7.83/8.02  thf(l54_zfmisc_1, axiom,
% 7.83/8.02    (![A:$i,B:$i,C:$i,D:$i]:
% 7.83/8.02     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 7.83/8.02       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 7.83/8.02  thf('31', plain,
% 7.83/8.02      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 7.83/8.02         ((r2_hidden @ X36 @ X37)
% 7.83/8.02          | ~ (r2_hidden @ (k4_tarski @ X36 @ X38) @ (k2_zfmisc_1 @ X37 @ X39)))),
% 7.83/8.02      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.83/8.02  thf('32', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.83/8.02         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 7.83/8.02             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 7.83/8.02          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['30', '31'])).
% 7.83/8.02  thf('33', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3)
% 7.83/8.02          | (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['25', '32'])).
% 7.83/8.02  thf('34', plain,
% 7.83/8.02      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.83/8.02        | (r2_hidden @ (sk_C @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_A)) @ 
% 7.83/8.02           (k1_tarski @ sk_A)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['24', '33'])).
% 7.83/8.02  thf('35', plain,
% 7.83/8.02      (![X3 : $i, X4 : $i]:
% 7.83/8.02         (~ (r2_xboole_0 @ X3 @ X4) | ~ (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 7.83/8.02      inference('cnf', [status(esa)], [t6_xboole_0])).
% 7.83/8.02  thf('36', plain,
% 7.83/8.02      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.83/8.02        | ~ (r2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_3)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['34', '35'])).
% 7.83/8.02  thf('37', plain,
% 7.83/8.02      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.83/8.02        | (r2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_3)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['17', '18'])).
% 7.83/8.02  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 7.83/8.02      inference('clc', [status(thm)], ['36', '37'])).
% 7.83/8.02  thf('39', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 7.83/8.02           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 7.83/8.02      inference('demod', [status(thm)], ['28', '29'])).
% 7.83/8.02  thf('40', plain,
% 7.83/8.02      (![X0 : $i]:
% 7.83/8.02         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ X0))
% 7.83/8.02           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 7.83/8.02      inference('sup+', [status(thm)], ['38', '39'])).
% 7.83/8.02  thf('41', plain,
% 7.83/8.02      (((sk_C_3) = (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_B)))),
% 7.83/8.02      inference('demod', [status(thm)], ['0', '40'])).
% 7.83/8.02  thf(d5_relat_1, axiom,
% 7.83/8.02    (![A:$i,B:$i]:
% 7.83/8.02     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 7.83/8.02       ( ![C:$i]:
% 7.83/8.02         ( ( r2_hidden @ C @ B ) <=>
% 7.83/8.02           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 7.83/8.02  thf('42', plain,
% 7.83/8.02      (![X58 : $i, X61 : $i]:
% 7.83/8.02         (((X61) = (k2_relat_1 @ X58))
% 7.83/8.02          | (r2_hidden @ 
% 7.83/8.02             (k4_tarski @ (sk_D_2 @ X61 @ X58) @ (sk_C_2 @ X61 @ X58)) @ X58)
% 7.83/8.02          | (r2_hidden @ (sk_C_2 @ X61 @ X58) @ X61))),
% 7.83/8.02      inference('cnf', [status(esa)], [d5_relat_1])).
% 7.83/8.02  thf('43', plain,
% 7.83/8.02      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 7.83/8.02         ((r2_hidden @ X38 @ X39)
% 7.83/8.02          | ~ (r2_hidden @ (k4_tarski @ X36 @ X38) @ (k2_zfmisc_1 @ X37 @ X39)))),
% 7.83/8.02      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.83/8.02  thf('44', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.83/8.02         ((r2_hidden @ (sk_C_2 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 7.83/8.02          | ((X2) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 7.83/8.02          | (r2_hidden @ (sk_C_2 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['42', '43'])).
% 7.83/8.02  thf('45', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         ((r2_hidden @ (sk_C_2 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 7.83/8.02          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 7.83/8.02      inference('eq_fact', [status(thm)], ['44'])).
% 7.83/8.02  thf('46', plain,
% 7.83/8.02      (((r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 7.83/8.02         (k1_tarski @ sk_B))
% 7.83/8.02        | ((k1_tarski @ sk_B)
% 7.83/8.02            = (k2_relat_1 @ 
% 7.83/8.02               (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_B)))))),
% 7.83/8.02      inference('sup+', [status(thm)], ['41', '45'])).
% 7.83/8.02  thf('47', plain,
% 7.83/8.02      (((sk_C_3) = (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_B)))),
% 7.83/8.02      inference('demod', [status(thm)], ['0', '40'])).
% 7.83/8.02  thf('48', plain,
% 7.83/8.02      (((r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 7.83/8.02         (k1_tarski @ sk_B))
% 7.83/8.02        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 7.83/8.02      inference('demod', [status(thm)], ['46', '47'])).
% 7.83/8.02  thf('49', plain,
% 7.83/8.02      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))
% 7.83/8.02        | ((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))),
% 7.83/8.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.83/8.02  thf('50', plain,
% 7.83/8.02      ((((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))
% 7.83/8.02         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 7.83/8.02      inference('split', [status(esa)], ['49'])).
% 7.83/8.02  thf('51', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 7.83/8.02      inference('clc', [status(thm)], ['36', '37'])).
% 7.83/8.02  thf('52', plain,
% 7.83/8.02      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A)))
% 7.83/8.02         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 7.83/8.02      inference('split', [status(esa)], ['49'])).
% 7.83/8.02  thf('53', plain,
% 7.83/8.02      ((((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_C_3)))
% 7.83/8.02         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 7.83/8.02      inference('sup-', [status(thm)], ['51', '52'])).
% 7.83/8.02  thf('54', plain, ((((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 7.83/8.02      inference('simplify', [status(thm)], ['53'])).
% 7.83/8.02  thf('55', plain,
% 7.83/8.02      (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))) | 
% 7.83/8.02       ~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 7.83/8.02      inference('split', [status(esa)], ['49'])).
% 7.83/8.02  thf('56', plain, (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 7.83/8.02      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 7.83/8.02  thf('57', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 7.83/8.02      inference('simpl_trail', [status(thm)], ['50', '56'])).
% 7.83/8.02  thf('58', plain,
% 7.83/8.02      ((r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ (k1_tarski @ sk_B))),
% 7.83/8.02      inference('simplify_reflect-', [status(thm)], ['48', '57'])).
% 7.83/8.02  thf('59', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.83/8.02      inference('sup+', [status(thm)], ['2', '6'])).
% 7.83/8.02  thf('60', plain,
% 7.83/8.02      (![X45 : $i, X47 : $i, X48 : $i]:
% 7.83/8.02         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 7.83/8.02          | ~ (r2_hidden @ X47 @ X48)
% 7.83/8.02          | ~ (r2_hidden @ X45 @ X48))),
% 7.83/8.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 7.83/8.02  thf('61', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 7.83/8.02          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['59', '60'])).
% 7.83/8.02  thf('62', plain,
% 7.83/8.02      ((r1_tarski @ 
% 7.83/8.02        (k2_tarski @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ sk_B) @ 
% 7.83/8.02        (k1_tarski @ sk_B))),
% 7.83/8.02      inference('sup-', [status(thm)], ['58', '61'])).
% 7.83/8.02  thf('63', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 7.83/8.02      inference('simplify', [status(thm)], ['3'])).
% 7.83/8.02  thf('64', plain,
% 7.83/8.02      (![X45 : $i, X46 : $i, X47 : $i]:
% 7.83/8.02         ((r2_hidden @ X47 @ X46)
% 7.83/8.02          | ~ (r1_tarski @ (k2_tarski @ X45 @ X47) @ X46))),
% 7.83/8.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 7.83/8.02  thf('65', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['63', '64'])).
% 7.83/8.02  thf('66', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['4', '5'])).
% 7.83/8.02  thf('67', plain,
% 7.83/8.02      (![X45 : $i, X47 : $i, X48 : $i]:
% 7.83/8.02         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 7.83/8.02          | ~ (r2_hidden @ X47 @ X48)
% 7.83/8.02          | ~ (r2_hidden @ X45 @ X48))),
% 7.83/8.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 7.83/8.02  thf('68', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.83/8.02         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 7.83/8.02          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['66', '67'])).
% 7.83/8.02  thf('69', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['65', '68'])).
% 7.83/8.02  thf('70', plain,
% 7.83/8.02      (![X5 : $i, X7 : $i]:
% 7.83/8.02         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 7.83/8.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.83/8.02  thf('71', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 7.83/8.02          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['69', '70'])).
% 7.83/8.02  thf('72', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['65', '68'])).
% 7.83/8.02  thf('73', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 7.83/8.02      inference('demod', [status(thm)], ['71', '72'])).
% 7.83/8.02  thf('74', plain,
% 7.83/8.02      ((r1_tarski @ 
% 7.83/8.02        (k2_tarski @ sk_B @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3)) @ 
% 7.83/8.02        (k1_tarski @ sk_B))),
% 7.83/8.02      inference('demod', [status(thm)], ['62', '73'])).
% 7.83/8.02  thf('75', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['4', '5'])).
% 7.83/8.02  thf('76', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.83/8.02         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 7.83/8.02          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['66', '67'])).
% 7.83/8.02  thf('77', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['75', '76'])).
% 7.83/8.02  thf('78', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 7.83/8.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.83/8.02  thf('79', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('demod', [status(thm)], ['77', '78'])).
% 7.83/8.02  thf('80', plain,
% 7.83/8.02      (![X5 : $i, X7 : $i]:
% 7.83/8.02         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 7.83/8.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.83/8.02  thf('81', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 7.83/8.02          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['79', '80'])).
% 7.83/8.02  thf('82', plain,
% 7.83/8.02      (((k2_tarski @ sk_B @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3))
% 7.83/8.02         = (k1_tarski @ sk_B))),
% 7.83/8.02      inference('sup-', [status(thm)], ['74', '81'])).
% 7.83/8.02  thf('83', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 7.83/8.02      inference('sup-', [status(thm)], ['8', '10'])).
% 7.83/8.02  thf('84', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 7.83/8.02      inference('sup-', [status(thm)], ['63', '64'])).
% 7.83/8.02  thf('85', plain,
% 7.83/8.02      (![X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 7.83/8.02         ((r2_hidden @ (k4_tarski @ X36 @ X38) @ (k2_zfmisc_1 @ X37 @ X40))
% 7.83/8.02          | ~ (r2_hidden @ X38 @ X40)
% 7.83/8.02          | ~ (r2_hidden @ X36 @ X37))),
% 7.83/8.02      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.83/8.02  thf('86', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.83/8.02         (~ (r2_hidden @ X3 @ X2)
% 7.83/8.02          | (r2_hidden @ (k4_tarski @ X3 @ X0) @ 
% 7.83/8.02             (k2_zfmisc_1 @ X2 @ (k2_tarski @ X1 @ X0))))),
% 7.83/8.02      inference('sup-', [status(thm)], ['84', '85'])).
% 7.83/8.02  thf('87', plain,
% 7.83/8.02      (![X0 : $i, X1 : $i]:
% 7.83/8.02         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 7.83/8.02          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k2_tarski @ X1 @ X0)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['83', '86'])).
% 7.83/8.02  thf('88', plain,
% 7.83/8.02      ((r2_hidden @ 
% 7.83/8.02        (k4_tarski @ sk_A @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3)) @ 
% 7.83/8.02        (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_B)))),
% 7.83/8.02      inference('sup+', [status(thm)], ['82', '87'])).
% 7.83/8.02  thf('89', plain,
% 7.83/8.02      (((sk_C_3) = (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_B)))),
% 7.83/8.02      inference('demod', [status(thm)], ['0', '40'])).
% 7.83/8.02  thf('90', plain,
% 7.83/8.02      ((r2_hidden @ 
% 7.83/8.02        (k4_tarski @ sk_A @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3)) @ sk_C_3)),
% 7.83/8.02      inference('demod', [status(thm)], ['88', '89'])).
% 7.83/8.02  thf('91', plain,
% 7.83/8.02      (![X58 : $i, X61 : $i, X62 : $i]:
% 7.83/8.02         (((X61) = (k2_relat_1 @ X58))
% 7.83/8.02          | ~ (r2_hidden @ (k4_tarski @ X62 @ (sk_C_2 @ X61 @ X58)) @ X58)
% 7.83/8.02          | ~ (r2_hidden @ (sk_C_2 @ X61 @ X58) @ X61))),
% 7.83/8.02      inference('cnf', [status(esa)], [d5_relat_1])).
% 7.83/8.02  thf('92', plain,
% 7.83/8.02      ((~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 7.83/8.02           (k1_tarski @ sk_B))
% 7.83/8.02        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 7.83/8.02      inference('sup-', [status(thm)], ['90', '91'])).
% 7.83/8.02  thf('93', plain,
% 7.83/8.02      ((r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ (k1_tarski @ sk_B))),
% 7.83/8.02      inference('simplify_reflect-', [status(thm)], ['48', '57'])).
% 7.83/8.02  thf('94', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))),
% 7.83/8.02      inference('demod', [status(thm)], ['92', '93'])).
% 7.83/8.02  thf('95', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 7.83/8.02      inference('simpl_trail', [status(thm)], ['50', '56'])).
% 7.83/8.02  thf('96', plain, ($false),
% 7.83/8.02      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 7.83/8.02  
% 7.83/8.02  % SZS output end Refutation
% 7.83/8.02  
% 7.83/8.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
