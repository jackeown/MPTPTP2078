%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.irT1jvl6Vt

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:42 EST 2020

% Result     : Theorem 4.40s
% Output     : Refutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 159 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  806 (1556 expanded)
%              Number of equality atoms :   61 ( 134 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

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
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i,X48: $i,X50: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X47 @ X48 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X50 ) ) )
      | ( X48 != X50 )
      | ( X47 != X46 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('2',plain,(
    ! [X46: $i,X50: $i] :
      ( r2_hidden @ ( k4_tarski @ X46 @ X50 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ~ ( r2_hidden @ ( k4_tarski @ X37 @ X38 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X36 ) @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_4 ),
    inference('sup+',[status(thm)],['0','4'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('6',plain,(
    ! [X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X65 @ X66 ) @ X67 )
      | ( r2_hidden @ X66 @ X68 )
      | ( X68
       != ( k2_relat_1 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( r2_hidden @ X66 @ ( k2_relat_1 @ X67 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X65 @ X66 ) @ X67 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X37 @ X38 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X36 ) @ X40 ) )
      | ~ ( r2_hidden @ X38 @ X40 )
      | ( X37 != X36 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('11',plain,(
    ! [X36: $i,X38: $i,X40: $i] :
      ( ~ ( r2_hidden @ X38 @ X40 )
      | ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X36 ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('13',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X43 = X44 )
      | ~ ( r2_hidden @ ( k4_tarski @ X41 @ X43 ) @ ( k2_zfmisc_1 @ X42 @ ( k1_tarski @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_relat_1 @ sk_C_4 )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('22',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( r2_hidden @ X69 @ X68 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X69 @ X67 ) @ X69 ) @ X67 )
      | ( X68
       != ( k2_relat_1 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('24',plain,(
    ! [X67: $i,X69: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X69 @ X67 ) @ X69 ) @ X67 )
      | ~ ( r2_hidden @ X69 @ ( k2_relat_1 @ X67 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('27',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X51 ) @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X51 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X43 = X44 )
      | ~ ( r2_hidden @ ( k4_tarski @ X41 @ X43 ) @ ( k2_zfmisc_1 @ X42 @ ( k1_tarski @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_4 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_4 ) )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['20','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_4 ),
    inference('sup+',[status(thm)],['0','4'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('44',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X58 @ X59 ) @ X60 )
      | ( r2_hidden @ X58 @ X61 )
      | ( X61
       != ( k1_relat_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('45',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( r2_hidden @ X58 @ ( k1_relat_1 @ X60 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X58 @ X59 ) @ X60 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('48',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_4 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X62 @ X61 )
      | ( r2_hidden @ ( k4_tarski @ X62 @ ( sk_D_1 @ X62 @ X60 ) ) @ X60 )
      | ( X61
       != ( k1_relat_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('54',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X62 @ ( sk_D_1 @ X62 @ X60 ) ) @ X60 )
      | ~ ( r2_hidden @ X62 @ ( k1_relat_1 @ X60 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('58',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X37 = X36 )
      | ~ ( r2_hidden @ ( k4_tarski @ X37 @ X38 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X36 ) @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_4 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_4 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['50','65'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_relat_1 @ sk_C_4 ) )
   <= ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['42','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.irT1jvl6Vt
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:08:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 4.40/4.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.40/4.59  % Solved by: fo/fo7.sh
% 4.40/4.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.40/4.59  % done 6878 iterations in 4.133s
% 4.40/4.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.40/4.59  % SZS output start Refutation
% 4.40/4.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.40/4.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.40/4.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.40/4.59  thf(sk_A_type, type, sk_A: $i).
% 4.40/4.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.40/4.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.40/4.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.40/4.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.40/4.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.40/4.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.40/4.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.40/4.59  thf(sk_C_4_type, type, sk_C_4: $i).
% 4.40/4.59  thf(sk_B_type, type, sk_B: $i).
% 4.40/4.59  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 4.40/4.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 4.40/4.59  thf(t23_relat_1, conjecture,
% 4.40/4.59    (![A:$i,B:$i,C:$i]:
% 4.40/4.59     ( ( v1_relat_1 @ C ) =>
% 4.40/4.59       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 4.40/4.59         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 4.40/4.59           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 4.40/4.59  thf(zf_stmt_0, negated_conjecture,
% 4.40/4.59    (~( ![A:$i,B:$i,C:$i]:
% 4.40/4.59        ( ( v1_relat_1 @ C ) =>
% 4.40/4.59          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 4.40/4.59            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 4.40/4.59              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 4.40/4.59    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 4.40/4.59  thf('0', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 4.40/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.59  thf(t34_zfmisc_1, axiom,
% 4.40/4.59    (![A:$i,B:$i,C:$i,D:$i]:
% 4.40/4.59     ( ( r2_hidden @
% 4.40/4.59         ( k4_tarski @ A @ B ) @ 
% 4.40/4.59         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 4.40/4.59       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 4.40/4.59  thf('1', plain,
% 4.40/4.59      (![X46 : $i, X47 : $i, X48 : $i, X50 : $i]:
% 4.40/4.59         ((r2_hidden @ (k4_tarski @ X47 @ X48) @ 
% 4.40/4.59           (k2_zfmisc_1 @ (k1_tarski @ X46) @ (k1_tarski @ X50)))
% 4.40/4.59          | ((X48) != (X50))
% 4.40/4.59          | ((X47) != (X46)))),
% 4.40/4.59      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 4.40/4.59  thf('2', plain,
% 4.40/4.59      (![X46 : $i, X50 : $i]:
% 4.40/4.59         (r2_hidden @ (k4_tarski @ X46 @ X50) @ 
% 4.40/4.59          (k2_zfmisc_1 @ (k1_tarski @ X46) @ (k1_tarski @ X50)))),
% 4.40/4.59      inference('simplify', [status(thm)], ['1'])).
% 4.40/4.59  thf(t128_zfmisc_1, axiom,
% 4.40/4.59    (![A:$i,B:$i,C:$i,D:$i]:
% 4.40/4.59     ( ( r2_hidden @
% 4.40/4.59         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 4.40/4.59       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 4.40/4.59  thf('3', plain,
% 4.40/4.59      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 4.40/4.59         ((r2_hidden @ X38 @ X39)
% 4.40/4.59          | ~ (r2_hidden @ (k4_tarski @ X37 @ X38) @ 
% 4.40/4.59               (k2_zfmisc_1 @ (k1_tarski @ X36) @ X39)))),
% 4.40/4.59      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 4.40/4.59  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.40/4.59      inference('sup-', [status(thm)], ['2', '3'])).
% 4.40/4.59  thf('5', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_4)),
% 4.40/4.59      inference('sup+', [status(thm)], ['0', '4'])).
% 4.40/4.59  thf(d5_relat_1, axiom,
% 4.40/4.59    (![A:$i,B:$i]:
% 4.40/4.59     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 4.40/4.59       ( ![C:$i]:
% 4.40/4.59         ( ( r2_hidden @ C @ B ) <=>
% 4.40/4.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 4.40/4.59  thf('6', plain,
% 4.40/4.59      (![X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 4.40/4.59         (~ (r2_hidden @ (k4_tarski @ X65 @ X66) @ X67)
% 4.40/4.59          | (r2_hidden @ X66 @ X68)
% 4.40/4.59          | ((X68) != (k2_relat_1 @ X67)))),
% 4.40/4.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 4.40/4.59  thf('7', plain,
% 4.40/4.59      (![X65 : $i, X66 : $i, X67 : $i]:
% 4.40/4.59         ((r2_hidden @ X66 @ (k2_relat_1 @ X67))
% 4.40/4.59          | ~ (r2_hidden @ (k4_tarski @ X65 @ X66) @ X67))),
% 4.40/4.59      inference('simplify', [status(thm)], ['6'])).
% 4.40/4.59  thf('8', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_4))),
% 4.40/4.59      inference('sup-', [status(thm)], ['5', '7'])).
% 4.40/4.59  thf(d3_tarski, axiom,
% 4.40/4.59    (![A:$i,B:$i]:
% 4.40/4.59     ( ( r1_tarski @ A @ B ) <=>
% 4.40/4.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.40/4.59  thf('9', plain,
% 4.40/4.59      (![X3 : $i, X5 : $i]:
% 4.40/4.59         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 4.40/4.59      inference('cnf', [status(esa)], [d3_tarski])).
% 4.40/4.59  thf('10', plain,
% 4.40/4.59      (![X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 4.40/4.59         ((r2_hidden @ (k4_tarski @ X37 @ X38) @ 
% 4.40/4.59           (k2_zfmisc_1 @ (k1_tarski @ X36) @ X40))
% 4.40/4.59          | ~ (r2_hidden @ X38 @ X40)
% 4.40/4.59          | ((X37) != (X36)))),
% 4.40/4.59      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 4.40/4.59  thf('11', plain,
% 4.40/4.59      (![X36 : $i, X38 : $i, X40 : $i]:
% 4.40/4.59         (~ (r2_hidden @ X38 @ X40)
% 4.40/4.59          | (r2_hidden @ (k4_tarski @ X36 @ X38) @ 
% 4.40/4.59             (k2_zfmisc_1 @ (k1_tarski @ X36) @ X40)))),
% 4.40/4.59      inference('simplify', [status(thm)], ['10'])).
% 4.40/4.59  thf('12', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.40/4.59         ((r1_tarski @ X0 @ X1)
% 4.40/4.59          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ X1 @ X0)) @ 
% 4.40/4.59             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['9', '11'])).
% 4.40/4.59  thf(t129_zfmisc_1, axiom,
% 4.40/4.59    (![A:$i,B:$i,C:$i,D:$i]:
% 4.40/4.59     ( ( r2_hidden @
% 4.40/4.59         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 4.40/4.59       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 4.40/4.59  thf('13', plain,
% 4.40/4.59      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 4.40/4.59         (((X43) = (X44))
% 4.40/4.59          | ~ (r2_hidden @ (k4_tarski @ X41 @ X43) @ 
% 4.40/4.59               (k2_zfmisc_1 @ X42 @ (k1_tarski @ X44))))),
% 4.40/4.59      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 4.40/4.59  thf('14', plain,
% 4.40/4.59      (![X0 : $i, X2 : $i]:
% 4.40/4.59         ((r1_tarski @ (k1_tarski @ X0) @ X2)
% 4.40/4.59          | ((sk_C @ X2 @ (k1_tarski @ X0)) = (X0)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['12', '13'])).
% 4.40/4.59  thf('15', plain,
% 4.40/4.59      (![X3 : $i, X5 : $i]:
% 4.40/4.59         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 4.40/4.59      inference('cnf', [status(esa)], [d3_tarski])).
% 4.40/4.59  thf('16', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         (~ (r2_hidden @ X0 @ X1)
% 4.40/4.59          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 4.40/4.59          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 4.40/4.59      inference('sup-', [status(thm)], ['14', '15'])).
% 4.40/4.59  thf('17', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 4.40/4.59      inference('simplify', [status(thm)], ['16'])).
% 4.40/4.59  thf('18', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k2_relat_1 @ sk_C_4))),
% 4.40/4.59      inference('sup-', [status(thm)], ['8', '17'])).
% 4.40/4.59  thf(d10_xboole_0, axiom,
% 4.40/4.59    (![A:$i,B:$i]:
% 4.40/4.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.40/4.59  thf('19', plain,
% 4.40/4.59      (![X13 : $i, X15 : $i]:
% 4.40/4.59         (((X13) = (X15))
% 4.40/4.59          | ~ (r1_tarski @ X15 @ X13)
% 4.40/4.59          | ~ (r1_tarski @ X13 @ X15))),
% 4.40/4.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.40/4.59  thf('20', plain,
% 4.40/4.59      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_4) @ (k1_tarski @ sk_B))
% 4.40/4.59        | ((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['18', '19'])).
% 4.40/4.59  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.40/4.59      inference('sup-', [status(thm)], ['2', '3'])).
% 4.40/4.59  thf('22', plain,
% 4.40/4.59      (![X3 : $i, X5 : $i]:
% 4.40/4.59         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 4.40/4.59      inference('cnf', [status(esa)], [d3_tarski])).
% 4.40/4.59  thf('23', plain,
% 4.40/4.59      (![X67 : $i, X68 : $i, X69 : $i]:
% 4.40/4.59         (~ (r2_hidden @ X69 @ X68)
% 4.40/4.59          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X69 @ X67) @ X69) @ X67)
% 4.40/4.59          | ((X68) != (k2_relat_1 @ X67)))),
% 4.40/4.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 4.40/4.59  thf('24', plain,
% 4.40/4.59      (![X67 : $i, X69 : $i]:
% 4.40/4.59         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X69 @ X67) @ X69) @ X67)
% 4.40/4.59          | ~ (r2_hidden @ X69 @ (k2_relat_1 @ X67)))),
% 4.40/4.59      inference('simplify', [status(thm)], ['23'])).
% 4.40/4.59  thf('25', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 4.40/4.59          | (r2_hidden @ 
% 4.40/4.59             (k4_tarski @ (sk_D_3 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 4.40/4.59              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 4.40/4.59             X0))),
% 4.40/4.59      inference('sup-', [status(thm)], ['22', '24'])).
% 4.40/4.59  thf('26', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 4.40/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.59  thf(t36_zfmisc_1, axiom,
% 4.40/4.59    (![A:$i,B:$i,C:$i]:
% 4.40/4.59     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 4.40/4.59         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 4.40/4.59       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 4.40/4.59         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 4.40/4.59  thf('27', plain,
% 4.40/4.59      (![X51 : $i, X52 : $i, X53 : $i]:
% 4.40/4.59         ((k2_zfmisc_1 @ (k1_tarski @ X51) @ (k2_tarski @ X52 @ X53))
% 4.40/4.59           = (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X51 @ X53)))),
% 4.40/4.59      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 4.40/4.59  thf(t69_enumset1, axiom,
% 4.40/4.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.40/4.59  thf('28', plain,
% 4.40/4.59      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 4.40/4.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.40/4.59  thf('29', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 4.40/4.59           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.40/4.59      inference('sup+', [status(thm)], ['27', '28'])).
% 4.40/4.59  thf('30', plain,
% 4.40/4.59      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 4.40/4.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.40/4.59  thf('31', plain,
% 4.40/4.59      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 4.40/4.59         (((X43) = (X44))
% 4.40/4.59          | ~ (r2_hidden @ (k4_tarski @ X41 @ X43) @ 
% 4.40/4.59               (k2_zfmisc_1 @ X42 @ (k1_tarski @ X44))))),
% 4.40/4.59      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 4.40/4.59  thf('32', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.40/4.59         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.40/4.59             (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 4.40/4.59          | ((X2) = (X0)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['30', '31'])).
% 4.40/4.59  thf('33', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.40/4.59         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.40/4.59             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 4.40/4.59          | ((X2) = (X0)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['29', '32'])).
% 4.40/4.59  thf('34', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_4) | ((X0) = (sk_B)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['26', '33'])).
% 4.40/4.59  thf('35', plain,
% 4.40/4.59      (![X0 : $i]:
% 4.40/4.59         ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ X0)
% 4.40/4.59          | ((sk_C @ X0 @ (k2_relat_1 @ sk_C_4)) = (sk_B)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['25', '34'])).
% 4.40/4.59  thf('36', plain,
% 4.40/4.59      (![X3 : $i, X5 : $i]:
% 4.40/4.59         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 4.40/4.59      inference('cnf', [status(esa)], [d3_tarski])).
% 4.40/4.59  thf('37', plain,
% 4.40/4.59      (![X0 : $i]:
% 4.40/4.59         (~ (r2_hidden @ sk_B @ X0)
% 4.40/4.59          | (r1_tarski @ (k2_relat_1 @ sk_C_4) @ X0)
% 4.40/4.59          | (r1_tarski @ (k2_relat_1 @ sk_C_4) @ X0))),
% 4.40/4.59      inference('sup-', [status(thm)], ['35', '36'])).
% 4.40/4.59  thf('38', plain,
% 4.40/4.59      (![X0 : $i]:
% 4.40/4.59         ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 4.40/4.59      inference('simplify', [status(thm)], ['37'])).
% 4.40/4.59  thf('39', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ (k1_tarski @ sk_B))),
% 4.40/4.59      inference('sup-', [status(thm)], ['21', '38'])).
% 4.40/4.59  thf('40', plain, (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))),
% 4.40/4.59      inference('demod', [status(thm)], ['20', '39'])).
% 4.40/4.59  thf('41', plain,
% 4.40/4.59      ((((k1_relat_1 @ sk_C_4) != (k1_tarski @ sk_A))
% 4.40/4.59        | ((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B)))),
% 4.40/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.59  thf('42', plain,
% 4.40/4.59      ((((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B)))
% 4.40/4.59         <= (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))))),
% 4.40/4.59      inference('split', [status(esa)], ['41'])).
% 4.40/4.59  thf('43', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_4)),
% 4.40/4.59      inference('sup+', [status(thm)], ['0', '4'])).
% 4.40/4.59  thf(d4_relat_1, axiom,
% 4.40/4.59    (![A:$i,B:$i]:
% 4.40/4.59     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 4.40/4.59       ( ![C:$i]:
% 4.40/4.59         ( ( r2_hidden @ C @ B ) <=>
% 4.40/4.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 4.40/4.59  thf('44', plain,
% 4.40/4.59      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 4.40/4.59         (~ (r2_hidden @ (k4_tarski @ X58 @ X59) @ X60)
% 4.40/4.59          | (r2_hidden @ X58 @ X61)
% 4.40/4.59          | ((X61) != (k1_relat_1 @ X60)))),
% 4.40/4.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 4.40/4.59  thf('45', plain,
% 4.40/4.59      (![X58 : $i, X59 : $i, X60 : $i]:
% 4.40/4.59         ((r2_hidden @ X58 @ (k1_relat_1 @ X60))
% 4.40/4.59          | ~ (r2_hidden @ (k4_tarski @ X58 @ X59) @ X60))),
% 4.40/4.59      inference('simplify', [status(thm)], ['44'])).
% 4.40/4.59  thf('46', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_4))),
% 4.40/4.59      inference('sup-', [status(thm)], ['43', '45'])).
% 4.40/4.59  thf('47', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 4.40/4.59      inference('simplify', [status(thm)], ['16'])).
% 4.40/4.59  thf('48', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_4))),
% 4.40/4.59      inference('sup-', [status(thm)], ['46', '47'])).
% 4.40/4.59  thf('49', plain,
% 4.40/4.59      (![X13 : $i, X15 : $i]:
% 4.40/4.59         (((X13) = (X15))
% 4.40/4.59          | ~ (r1_tarski @ X15 @ X13)
% 4.40/4.59          | ~ (r1_tarski @ X13 @ X15))),
% 4.40/4.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.40/4.59  thf('50', plain,
% 4.40/4.59      ((~ (r1_tarski @ (k1_relat_1 @ sk_C_4) @ (k1_tarski @ sk_A))
% 4.40/4.59        | ((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['48', '49'])).
% 4.40/4.59  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.40/4.59      inference('sup-', [status(thm)], ['2', '3'])).
% 4.40/4.59  thf('52', plain,
% 4.40/4.59      (![X3 : $i, X5 : $i]:
% 4.40/4.59         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 4.40/4.59      inference('cnf', [status(esa)], [d3_tarski])).
% 4.40/4.59  thf('53', plain,
% 4.40/4.59      (![X60 : $i, X61 : $i, X62 : $i]:
% 4.40/4.59         (~ (r2_hidden @ X62 @ X61)
% 4.40/4.59          | (r2_hidden @ (k4_tarski @ X62 @ (sk_D_1 @ X62 @ X60)) @ X60)
% 4.40/4.59          | ((X61) != (k1_relat_1 @ X60)))),
% 4.40/4.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 4.40/4.59  thf('54', plain,
% 4.40/4.59      (![X60 : $i, X62 : $i]:
% 4.40/4.59         ((r2_hidden @ (k4_tarski @ X62 @ (sk_D_1 @ X62 @ X60)) @ X60)
% 4.40/4.59          | ~ (r2_hidden @ X62 @ (k1_relat_1 @ X60)))),
% 4.40/4.59      inference('simplify', [status(thm)], ['53'])).
% 4.40/4.59  thf('55', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 4.40/4.59          | (r2_hidden @ 
% 4.40/4.59             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 4.40/4.59              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 4.40/4.59             X0))),
% 4.40/4.59      inference('sup-', [status(thm)], ['52', '54'])).
% 4.40/4.59  thf('56', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 4.40/4.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.59  thf('57', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 4.40/4.59           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 4.40/4.59      inference('sup+', [status(thm)], ['27', '28'])).
% 4.40/4.59  thf('58', plain,
% 4.40/4.59      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 4.40/4.59         (((X37) = (X36))
% 4.40/4.59          | ~ (r2_hidden @ (k4_tarski @ X37 @ X38) @ 
% 4.40/4.59               (k2_zfmisc_1 @ (k1_tarski @ X36) @ X39)))),
% 4.40/4.59      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 4.40/4.59  thf('59', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.40/4.59         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 4.40/4.59             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 4.40/4.59          | ((X3) = (X1)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['57', '58'])).
% 4.40/4.59  thf('60', plain,
% 4.40/4.59      (![X0 : $i, X1 : $i]:
% 4.40/4.59         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_4) | ((X1) = (sk_A)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['56', '59'])).
% 4.40/4.59  thf('61', plain,
% 4.40/4.59      (![X0 : $i]:
% 4.40/4.59         ((r1_tarski @ (k1_relat_1 @ sk_C_4) @ X0)
% 4.40/4.59          | ((sk_C @ X0 @ (k1_relat_1 @ sk_C_4)) = (sk_A)))),
% 4.40/4.59      inference('sup-', [status(thm)], ['55', '60'])).
% 4.40/4.59  thf('62', plain,
% 4.40/4.59      (![X3 : $i, X5 : $i]:
% 4.40/4.59         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 4.40/4.59      inference('cnf', [status(esa)], [d3_tarski])).
% 4.40/4.59  thf('63', plain,
% 4.40/4.59      (![X0 : $i]:
% 4.40/4.59         (~ (r2_hidden @ sk_A @ X0)
% 4.40/4.59          | (r1_tarski @ (k1_relat_1 @ sk_C_4) @ X0)
% 4.40/4.59          | (r1_tarski @ (k1_relat_1 @ sk_C_4) @ X0))),
% 4.40/4.59      inference('sup-', [status(thm)], ['61', '62'])).
% 4.40/4.59  thf('64', plain,
% 4.40/4.59      (![X0 : $i]:
% 4.40/4.59         ((r1_tarski @ (k1_relat_1 @ sk_C_4) @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 4.40/4.59      inference('simplify', [status(thm)], ['63'])).
% 4.40/4.59  thf('65', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_4) @ (k1_tarski @ sk_A))),
% 4.40/4.59      inference('sup-', [status(thm)], ['51', '64'])).
% 4.40/4.59  thf('66', plain, (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))),
% 4.40/4.59      inference('demod', [status(thm)], ['50', '65'])).
% 4.40/4.59  thf('67', plain,
% 4.40/4.59      ((((k1_relat_1 @ sk_C_4) != (k1_tarski @ sk_A)))
% 4.40/4.59         <= (~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))))),
% 4.40/4.59      inference('split', [status(esa)], ['41'])).
% 4.40/4.59  thf('68', plain,
% 4.40/4.59      ((((k1_relat_1 @ sk_C_4) != (k1_relat_1 @ sk_C_4)))
% 4.40/4.59         <= (~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))))),
% 4.40/4.59      inference('sup-', [status(thm)], ['66', '67'])).
% 4.40/4.59  thf('69', plain, ((((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 4.40/4.59      inference('simplify', [status(thm)], ['68'])).
% 4.40/4.59  thf('70', plain,
% 4.40/4.59      (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))) | 
% 4.40/4.59       ~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 4.40/4.59      inference('split', [status(esa)], ['41'])).
% 4.40/4.59  thf('71', plain, (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B)))),
% 4.40/4.59      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 4.40/4.59  thf('72', plain, (((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B))),
% 4.40/4.59      inference('simpl_trail', [status(thm)], ['42', '71'])).
% 4.40/4.59  thf('73', plain, ($false),
% 4.40/4.59      inference('simplify_reflect-', [status(thm)], ['40', '72'])).
% 4.40/4.59  
% 4.40/4.59  % SZS output end Refutation
% 4.40/4.59  
% 4.40/4.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
