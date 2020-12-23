%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a9ysEasWDU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:42 EST 2020

% Result     : Theorem 3.70s
% Output     : Refutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 279 expanded)
%              Number of leaves         :   27 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  873 (2423 expanded)
%              Number of equality atoms :   72 ( 282 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

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

thf('1',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('2',plain,(
    ! [X46: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('3',plain,
    ( ( k1_setfam_1 @ sk_C_4 )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k1_setfam_1 @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X42 @ X43 )
      | ~ ( r1_tarski @ ( k2_tarski @ X42 @ X44 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    r2_hidden @ ( k1_setfam_1 @ sk_C_4 ) @ sk_C_4 ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( k1_setfam_1 @ sk_C_4 )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('13',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X56 @ X57 ) @ X58 )
      | ( r2_hidden @ X57 @ X59 )
      | ( X59
       != ( k2_relat_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('14',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( r2_hidden @ X57 @ ( k2_relat_1 @ X58 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X56 @ X57 ) @ X58 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_setfam_1 @ sk_C_4 ) @ X0 )
      | ( r2_hidden @ sk_B @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('18',plain,(
    ! [X42: $i,X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X42 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( r2_hidden @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_4 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_relat_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_relat_1 @ sk_C_4 )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( r2_hidden @ X60 @ X59 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X60 @ X58 ) @ X60 ) @ X58 )
      | ( X59
       != ( k2_relat_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('28',plain,(
    ! [X58: $i,X60: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X60 @ X58 ) @ X60 ) @ X58 )
      | ~ ( r2_hidden @ X60 @ ( k2_relat_1 @ X58 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( k1_setfam_1 @ sk_C_4 )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('31',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X38 ) @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_tarski @ ( k4_tarski @ X38 @ X39 ) @ ( k4_tarski @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X30 = X31 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ ( k1_tarski @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_tarski @ ( k1_setfam_1 @ sk_C_4 ) ) )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k1_setfam_1 @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_4 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_4 ) )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['25','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['24','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
    r2_hidden @ ( k1_setfam_1 @ sk_C_4 ) @ sk_C_4 ),
    inference('sup+',[status(thm)],['4','10'])).

thf('50',plain,
    ( ( k1_setfam_1 @ sk_C_4 )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('51',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X49 @ X50 ) @ X51 )
      | ( r2_hidden @ X49 @ X52 )
      | ( X52
       != ( k1_relat_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('52',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ X49 @ ( k1_relat_1 @ X51 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X49 @ X50 ) @ X51 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_setfam_1 @ sk_C_4 ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('56',plain,(
    ! [X42: $i,X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X42 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( r2_hidden @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_4 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('60',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_4 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X53 @ X52 )
      | ( r2_hidden @ ( k4_tarski @ X53 @ ( sk_D_2 @ X53 @ X51 ) ) @ X51 )
      | ( X52
       != ( k1_relat_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('66',plain,(
    ! [X51: $i,X53: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X53 @ ( sk_D_2 @ X53 @ X51 ) ) @ X51 )
      | ~ ( r2_hidden @ X53 @ ( k1_relat_1 @ X51 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( k1_setfam_1 @ sk_C_4 )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('69',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('70',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X34 = X33 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X35 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_tarski @ ( k1_setfam_1 @ sk_C_4 ) ) )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,
    ( sk_C_4
    = ( k1_tarski @ ( k1_setfam_1 @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_4 )
      | ( X1 = sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_4 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_4 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['63','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['62','81'])).

thf('83',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_relat_1 @ sk_C_4 ) )
   <= ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( k2_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_4 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('87',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    ( k2_relat_1 @ sk_C_4 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['48','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a9ysEasWDU
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.70/3.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.70/3.92  % Solved by: fo/fo7.sh
% 3.70/3.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.70/3.92  % done 4468 iterations in 3.464s
% 3.70/3.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.70/3.92  % SZS output start Refutation
% 3.70/3.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.70/3.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.70/3.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.70/3.92  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.70/3.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.70/3.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.70/3.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.70/3.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.70/3.92  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.70/3.92  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 3.70/3.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.70/3.92  thf(sk_B_type, type, sk_B: $i).
% 3.70/3.92  thf(sk_A_type, type, sk_A: $i).
% 3.70/3.92  thf(sk_C_4_type, type, sk_C_4: $i).
% 3.70/3.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.70/3.92  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 3.70/3.92  thf(t23_relat_1, conjecture,
% 3.70/3.92    (![A:$i,B:$i,C:$i]:
% 3.70/3.92     ( ( v1_relat_1 @ C ) =>
% 3.70/3.92       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 3.70/3.92         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 3.70/3.92           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 3.70/3.92  thf(zf_stmt_0, negated_conjecture,
% 3.70/3.92    (~( ![A:$i,B:$i,C:$i]:
% 3.70/3.92        ( ( v1_relat_1 @ C ) =>
% 3.70/3.92          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 3.70/3.92            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 3.70/3.92              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 3.70/3.92    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 3.70/3.92  thf('0', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.70/3.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.92  thf('1', plain, (((sk_C_4) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.70/3.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.92  thf(t11_setfam_1, axiom,
% 3.70/3.92    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 3.70/3.92  thf('2', plain, (![X46 : $i]: ((k1_setfam_1 @ (k1_tarski @ X46)) = (X46))),
% 3.70/3.92      inference('cnf', [status(esa)], [t11_setfam_1])).
% 3.70/3.92  thf('3', plain, (((k1_setfam_1 @ sk_C_4) = (k4_tarski @ sk_A @ sk_B))),
% 3.70/3.92      inference('sup+', [status(thm)], ['1', '2'])).
% 3.70/3.92  thf('4', plain, (((sk_C_4) = (k1_tarski @ (k1_setfam_1 @ sk_C_4)))),
% 3.70/3.92      inference('demod', [status(thm)], ['0', '3'])).
% 3.70/3.92  thf(t69_enumset1, axiom,
% 3.70/3.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.70/3.92  thf('5', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 3.70/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.70/3.92  thf(d10_xboole_0, axiom,
% 3.70/3.92    (![A:$i,B:$i]:
% 3.70/3.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.70/3.92  thf('6', plain,
% 3.70/3.92      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 3.70/3.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.70/3.92  thf('7', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 3.70/3.92      inference('simplify', [status(thm)], ['6'])).
% 3.70/3.92  thf(t38_zfmisc_1, axiom,
% 3.70/3.92    (![A:$i,B:$i,C:$i]:
% 3.70/3.92     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 3.70/3.92       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 3.70/3.92  thf('8', plain,
% 3.70/3.92      (![X42 : $i, X43 : $i, X44 : $i]:
% 3.70/3.92         ((r2_hidden @ X42 @ X43)
% 3.70/3.92          | ~ (r1_tarski @ (k2_tarski @ X42 @ X44) @ X43))),
% 3.70/3.92      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 3.70/3.92  thf('9', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 3.70/3.92      inference('sup-', [status(thm)], ['7', '8'])).
% 3.70/3.92  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.70/3.92      inference('sup+', [status(thm)], ['5', '9'])).
% 3.70/3.92  thf('11', plain, ((r2_hidden @ (k1_setfam_1 @ sk_C_4) @ sk_C_4)),
% 3.70/3.92      inference('sup+', [status(thm)], ['4', '10'])).
% 3.70/3.92  thf('12', plain, (((k1_setfam_1 @ sk_C_4) = (k4_tarski @ sk_A @ sk_B))),
% 3.70/3.92      inference('sup+', [status(thm)], ['1', '2'])).
% 3.70/3.92  thf(d5_relat_1, axiom,
% 3.70/3.92    (![A:$i,B:$i]:
% 3.70/3.92     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.70/3.92       ( ![C:$i]:
% 3.70/3.92         ( ( r2_hidden @ C @ B ) <=>
% 3.70/3.92           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.70/3.92  thf('13', plain,
% 3.70/3.92      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X56 @ X57) @ X58)
% 3.70/3.92          | (r2_hidden @ X57 @ X59)
% 3.70/3.92          | ((X59) != (k2_relat_1 @ X58)))),
% 3.70/3.92      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.70/3.92  thf('14', plain,
% 3.70/3.92      (![X56 : $i, X57 : $i, X58 : $i]:
% 3.70/3.92         ((r2_hidden @ X57 @ (k2_relat_1 @ X58))
% 3.70/3.92          | ~ (r2_hidden @ (k4_tarski @ X56 @ X57) @ X58))),
% 3.70/3.92      inference('simplify', [status(thm)], ['13'])).
% 3.70/3.92  thf('15', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k1_setfam_1 @ sk_C_4) @ X0)
% 3.70/3.92          | (r2_hidden @ sk_B @ (k2_relat_1 @ X0)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['12', '14'])).
% 3.70/3.92  thf('16', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_4))),
% 3.70/3.92      inference('sup-', [status(thm)], ['11', '15'])).
% 3.70/3.92  thf('17', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_4))),
% 3.70/3.92      inference('sup-', [status(thm)], ['11', '15'])).
% 3.70/3.92  thf('18', plain,
% 3.70/3.92      (![X42 : $i, X44 : $i, X45 : $i]:
% 3.70/3.92         ((r1_tarski @ (k2_tarski @ X42 @ X44) @ X45)
% 3.70/3.92          | ~ (r2_hidden @ X44 @ X45)
% 3.70/3.92          | ~ (r2_hidden @ X42 @ X45))),
% 3.70/3.92      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 3.70/3.92  thf('19', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_4))
% 3.70/3.92          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_4)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['17', '18'])).
% 3.70/3.92  thf('20', plain,
% 3.70/3.92      ((r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ (k2_relat_1 @ sk_C_4))),
% 3.70/3.92      inference('sup-', [status(thm)], ['16', '19'])).
% 3.70/3.92  thf('21', plain,
% 3.70/3.92      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 3.70/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.70/3.92  thf('22', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k2_relat_1 @ sk_C_4))),
% 3.70/3.92      inference('demod', [status(thm)], ['20', '21'])).
% 3.70/3.92  thf('23', plain,
% 3.70/3.92      (![X10 : $i, X12 : $i]:
% 3.70/3.92         (((X10) = (X12))
% 3.70/3.92          | ~ (r1_tarski @ X12 @ X10)
% 3.70/3.92          | ~ (r1_tarski @ X10 @ X12))),
% 3.70/3.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.70/3.92  thf('24', plain,
% 3.70/3.92      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_4) @ (k1_tarski @ sk_B))
% 3.70/3.92        | ((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['22', '23'])).
% 3.70/3.92  thf('25', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.70/3.92      inference('sup+', [status(thm)], ['5', '9'])).
% 3.70/3.92  thf(d3_tarski, axiom,
% 3.70/3.92    (![A:$i,B:$i]:
% 3.70/3.92     ( ( r1_tarski @ A @ B ) <=>
% 3.70/3.92       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.70/3.92  thf('26', plain,
% 3.70/3.92      (![X1 : $i, X3 : $i]:
% 3.70/3.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.70/3.92      inference('cnf', [status(esa)], [d3_tarski])).
% 3.70/3.92  thf('27', plain,
% 3.70/3.92      (![X58 : $i, X59 : $i, X60 : $i]:
% 3.70/3.92         (~ (r2_hidden @ X60 @ X59)
% 3.70/3.92          | (r2_hidden @ (k4_tarski @ (sk_D_4 @ X60 @ X58) @ X60) @ X58)
% 3.70/3.92          | ((X59) != (k2_relat_1 @ X58)))),
% 3.70/3.92      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.70/3.92  thf('28', plain,
% 3.70/3.92      (![X58 : $i, X60 : $i]:
% 3.70/3.92         ((r2_hidden @ (k4_tarski @ (sk_D_4 @ X60 @ X58) @ X60) @ X58)
% 3.70/3.92          | ~ (r2_hidden @ X60 @ (k2_relat_1 @ X58)))),
% 3.70/3.92      inference('simplify', [status(thm)], ['27'])).
% 3.70/3.92  thf('29', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]:
% 3.70/3.92         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 3.70/3.92          | (r2_hidden @ 
% 3.70/3.92             (k4_tarski @ (sk_D_4 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 3.70/3.92              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 3.70/3.92             X0))),
% 3.70/3.92      inference('sup-', [status(thm)], ['26', '28'])).
% 3.70/3.92  thf('30', plain, (((k1_setfam_1 @ sk_C_4) = (k4_tarski @ sk_A @ sk_B))),
% 3.70/3.92      inference('sup+', [status(thm)], ['1', '2'])).
% 3.70/3.92  thf(t36_zfmisc_1, axiom,
% 3.70/3.92    (![A:$i,B:$i,C:$i]:
% 3.70/3.92     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 3.70/3.92         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 3.70/3.92       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 3.70/3.92         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 3.70/3.92  thf('31', plain,
% 3.70/3.92      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.70/3.92         ((k2_zfmisc_1 @ (k1_tarski @ X38) @ (k2_tarski @ X39 @ X40))
% 3.70/3.92           = (k2_tarski @ (k4_tarski @ X38 @ X39) @ (k4_tarski @ X38 @ X40)))),
% 3.70/3.92      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.70/3.92  thf('32', plain,
% 3.70/3.92      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 3.70/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.70/3.92  thf('33', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]:
% 3.70/3.92         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 3.70/3.92           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.70/3.92      inference('sup+', [status(thm)], ['31', '32'])).
% 3.70/3.92  thf('34', plain,
% 3.70/3.92      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 3.70/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.70/3.92  thf(t129_zfmisc_1, axiom,
% 3.70/3.92    (![A:$i,B:$i,C:$i,D:$i]:
% 3.70/3.92     ( ( r2_hidden @
% 3.70/3.92         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 3.70/3.92       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 3.70/3.92  thf('35', plain,
% 3.70/3.92      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.70/3.92         (((X30) = (X31))
% 3.70/3.92          | ~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ 
% 3.70/3.92               (k2_zfmisc_1 @ X29 @ (k1_tarski @ X31))))),
% 3.70/3.92      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 3.70/3.92  thf('36', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.70/3.92             (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 3.70/3.92          | ((X2) = (X0)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['34', '35'])).
% 3.70/3.92  thf('37', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.70/3.92             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.70/3.92          | ((X2) = (X0)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['33', '36'])).
% 3.70/3.92  thf('38', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 3.70/3.92             (k1_tarski @ (k1_setfam_1 @ sk_C_4)))
% 3.70/3.92          | ((X0) = (sk_B)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['30', '37'])).
% 3.70/3.92  thf('39', plain, (((sk_C_4) = (k1_tarski @ (k1_setfam_1 @ sk_C_4)))),
% 3.70/3.92      inference('demod', [status(thm)], ['0', '3'])).
% 3.70/3.92  thf('40', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_4) | ((X0) = (sk_B)))),
% 3.70/3.92      inference('demod', [status(thm)], ['38', '39'])).
% 3.70/3.92  thf('41', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ X0)
% 3.70/3.92          | ((sk_C @ X0 @ (k2_relat_1 @ sk_C_4)) = (sk_B)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['29', '40'])).
% 3.70/3.92  thf('42', plain,
% 3.70/3.92      (![X1 : $i, X3 : $i]:
% 3.70/3.92         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.70/3.92      inference('cnf', [status(esa)], [d3_tarski])).
% 3.70/3.92  thf('43', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         (~ (r2_hidden @ sk_B @ X0)
% 3.70/3.92          | (r1_tarski @ (k2_relat_1 @ sk_C_4) @ X0)
% 3.70/3.92          | (r1_tarski @ (k2_relat_1 @ sk_C_4) @ X0))),
% 3.70/3.92      inference('sup-', [status(thm)], ['41', '42'])).
% 3.70/3.92  thf('44', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 3.70/3.92      inference('simplify', [status(thm)], ['43'])).
% 3.70/3.92  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ (k1_tarski @ sk_B))),
% 3.70/3.92      inference('sup-', [status(thm)], ['25', '44'])).
% 3.70/3.92  thf('46', plain, (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))),
% 3.70/3.92      inference('demod', [status(thm)], ['24', '45'])).
% 3.70/3.92  thf('47', plain,
% 3.70/3.92      ((((k1_relat_1 @ sk_C_4) != (k1_tarski @ sk_A))
% 3.70/3.92        | ((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B)))),
% 3.70/3.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.92  thf('48', plain,
% 3.70/3.92      ((((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B)))
% 3.70/3.92         <= (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))))),
% 3.70/3.92      inference('split', [status(esa)], ['47'])).
% 3.70/3.92  thf('49', plain, ((r2_hidden @ (k1_setfam_1 @ sk_C_4) @ sk_C_4)),
% 3.70/3.92      inference('sup+', [status(thm)], ['4', '10'])).
% 3.70/3.92  thf('50', plain, (((k1_setfam_1 @ sk_C_4) = (k4_tarski @ sk_A @ sk_B))),
% 3.70/3.92      inference('sup+', [status(thm)], ['1', '2'])).
% 3.70/3.92  thf(d4_relat_1, axiom,
% 3.70/3.92    (![A:$i,B:$i]:
% 3.70/3.92     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.70/3.92       ( ![C:$i]:
% 3.70/3.92         ( ( r2_hidden @ C @ B ) <=>
% 3.70/3.92           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.70/3.92  thf('51', plain,
% 3.70/3.92      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X49 @ X50) @ X51)
% 3.70/3.92          | (r2_hidden @ X49 @ X52)
% 3.70/3.92          | ((X52) != (k1_relat_1 @ X51)))),
% 3.70/3.92      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.70/3.92  thf('52', plain,
% 3.70/3.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 3.70/3.92         ((r2_hidden @ X49 @ (k1_relat_1 @ X51))
% 3.70/3.92          | ~ (r2_hidden @ (k4_tarski @ X49 @ X50) @ X51))),
% 3.70/3.92      inference('simplify', [status(thm)], ['51'])).
% 3.70/3.92  thf('53', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k1_setfam_1 @ sk_C_4) @ X0)
% 3.70/3.92          | (r2_hidden @ sk_A @ (k1_relat_1 @ X0)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['50', '52'])).
% 3.70/3.92  thf('54', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_4))),
% 3.70/3.92      inference('sup-', [status(thm)], ['49', '53'])).
% 3.70/3.92  thf('55', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_4))),
% 3.70/3.92      inference('sup-', [status(thm)], ['49', '53'])).
% 3.70/3.92  thf('56', plain,
% 3.70/3.92      (![X42 : $i, X44 : $i, X45 : $i]:
% 3.70/3.92         ((r1_tarski @ (k2_tarski @ X42 @ X44) @ X45)
% 3.70/3.92          | ~ (r2_hidden @ X44 @ X45)
% 3.70/3.92          | ~ (r2_hidden @ X42 @ X45))),
% 3.70/3.92      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 3.70/3.92  thf('57', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_4))
% 3.70/3.92          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ (k1_relat_1 @ sk_C_4)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['55', '56'])).
% 3.70/3.92  thf('58', plain,
% 3.70/3.92      ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ (k1_relat_1 @ sk_C_4))),
% 3.70/3.92      inference('sup-', [status(thm)], ['54', '57'])).
% 3.70/3.92  thf('59', plain,
% 3.70/3.92      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 3.70/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.70/3.92  thf('60', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_4))),
% 3.70/3.92      inference('demod', [status(thm)], ['58', '59'])).
% 3.70/3.92  thf('61', plain,
% 3.70/3.92      (![X10 : $i, X12 : $i]:
% 3.70/3.92         (((X10) = (X12))
% 3.70/3.92          | ~ (r1_tarski @ X12 @ X10)
% 3.70/3.92          | ~ (r1_tarski @ X10 @ X12))),
% 3.70/3.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.70/3.92  thf('62', plain,
% 3.70/3.92      ((~ (r1_tarski @ (k1_relat_1 @ sk_C_4) @ (k1_tarski @ sk_A))
% 3.70/3.92        | ((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['60', '61'])).
% 3.70/3.92  thf('63', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.70/3.92      inference('sup+', [status(thm)], ['5', '9'])).
% 3.70/3.92  thf('64', plain,
% 3.70/3.92      (![X1 : $i, X3 : $i]:
% 3.70/3.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.70/3.92      inference('cnf', [status(esa)], [d3_tarski])).
% 3.70/3.92  thf('65', plain,
% 3.70/3.92      (![X51 : $i, X52 : $i, X53 : $i]:
% 3.70/3.92         (~ (r2_hidden @ X53 @ X52)
% 3.70/3.92          | (r2_hidden @ (k4_tarski @ X53 @ (sk_D_2 @ X53 @ X51)) @ X51)
% 3.70/3.92          | ((X52) != (k1_relat_1 @ X51)))),
% 3.70/3.92      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.70/3.92  thf('66', plain,
% 3.70/3.92      (![X51 : $i, X53 : $i]:
% 3.70/3.92         ((r2_hidden @ (k4_tarski @ X53 @ (sk_D_2 @ X53 @ X51)) @ X51)
% 3.70/3.92          | ~ (r2_hidden @ X53 @ (k1_relat_1 @ X51)))),
% 3.70/3.92      inference('simplify', [status(thm)], ['65'])).
% 3.70/3.92  thf('67', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]:
% 3.70/3.92         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.70/3.92          | (r2_hidden @ 
% 3.70/3.92             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 3.70/3.92              (sk_D_2 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 3.70/3.92             X0))),
% 3.70/3.92      inference('sup-', [status(thm)], ['64', '66'])).
% 3.70/3.92  thf('68', plain, (((k1_setfam_1 @ sk_C_4) = (k4_tarski @ sk_A @ sk_B))),
% 3.70/3.92      inference('sup+', [status(thm)], ['1', '2'])).
% 3.70/3.92  thf('69', plain,
% 3.70/3.92      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 3.70/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.70/3.92  thf(t34_zfmisc_1, axiom,
% 3.70/3.92    (![A:$i,B:$i,C:$i,D:$i]:
% 3.70/3.92     ( ( r2_hidden @
% 3.70/3.92         ( k4_tarski @ A @ B ) @ 
% 3.70/3.92         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 3.70/3.92       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 3.70/3.92  thf('70', plain,
% 3.70/3.92      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.70/3.92         (((X34) = (X33))
% 3.70/3.92          | ~ (r2_hidden @ (k4_tarski @ X34 @ X35) @ 
% 3.70/3.92               (k2_zfmisc_1 @ (k1_tarski @ X33) @ (k1_tarski @ X36))))),
% 3.70/3.92      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 3.70/3.92  thf('71', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.70/3.92             (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))
% 3.70/3.92          | ((X3) = (X1)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['69', '70'])).
% 3.70/3.92  thf('72', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]:
% 3.70/3.92         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 3.70/3.92           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.70/3.92      inference('sup+', [status(thm)], ['31', '32'])).
% 3.70/3.92  thf('73', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.70/3.92             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.70/3.92          | ((X3) = (X1)))),
% 3.70/3.92      inference('demod', [status(thm)], ['71', '72'])).
% 3.70/3.92  thf('74', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 3.70/3.92             (k1_tarski @ (k1_setfam_1 @ sk_C_4)))
% 3.70/3.92          | ((X1) = (sk_A)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['68', '73'])).
% 3.70/3.92  thf('75', plain, (((sk_C_4) = (k1_tarski @ (k1_setfam_1 @ sk_C_4)))),
% 3.70/3.92      inference('demod', [status(thm)], ['0', '3'])).
% 3.70/3.92  thf('76', plain,
% 3.70/3.92      (![X0 : $i, X1 : $i]:
% 3.70/3.92         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_4) | ((X1) = (sk_A)))),
% 3.70/3.92      inference('demod', [status(thm)], ['74', '75'])).
% 3.70/3.92  thf('77', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         ((r1_tarski @ (k1_relat_1 @ sk_C_4) @ X0)
% 3.70/3.92          | ((sk_C @ X0 @ (k1_relat_1 @ sk_C_4)) = (sk_A)))),
% 3.70/3.92      inference('sup-', [status(thm)], ['67', '76'])).
% 3.70/3.92  thf('78', plain,
% 3.70/3.92      (![X1 : $i, X3 : $i]:
% 3.70/3.92         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.70/3.92      inference('cnf', [status(esa)], [d3_tarski])).
% 3.70/3.92  thf('79', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         (~ (r2_hidden @ sk_A @ X0)
% 3.70/3.92          | (r1_tarski @ (k1_relat_1 @ sk_C_4) @ X0)
% 3.70/3.92          | (r1_tarski @ (k1_relat_1 @ sk_C_4) @ X0))),
% 3.70/3.92      inference('sup-', [status(thm)], ['77', '78'])).
% 3.70/3.92  thf('80', plain,
% 3.70/3.92      (![X0 : $i]:
% 3.70/3.92         ((r1_tarski @ (k1_relat_1 @ sk_C_4) @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 3.70/3.92      inference('simplify', [status(thm)], ['79'])).
% 3.70/3.92  thf('81', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_4) @ (k1_tarski @ sk_A))),
% 3.70/3.92      inference('sup-', [status(thm)], ['63', '80'])).
% 3.70/3.92  thf('82', plain, (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))),
% 3.70/3.92      inference('demod', [status(thm)], ['62', '81'])).
% 3.70/3.92  thf('83', plain,
% 3.70/3.92      ((((k1_relat_1 @ sk_C_4) != (k1_tarski @ sk_A)))
% 3.70/3.92         <= (~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))))),
% 3.70/3.92      inference('split', [status(esa)], ['47'])).
% 3.70/3.92  thf('84', plain,
% 3.70/3.92      ((((k1_relat_1 @ sk_C_4) != (k1_relat_1 @ sk_C_4)))
% 3.70/3.92         <= (~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A))))),
% 3.70/3.92      inference('sup-', [status(thm)], ['82', '83'])).
% 3.70/3.92  thf('85', plain, ((((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 3.70/3.92      inference('simplify', [status(thm)], ['84'])).
% 3.70/3.92  thf('86', plain,
% 3.70/3.92      (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B))) | 
% 3.70/3.92       ~ (((k1_relat_1 @ sk_C_4) = (k1_tarski @ sk_A)))),
% 3.70/3.92      inference('split', [status(esa)], ['47'])).
% 3.70/3.92  thf('87', plain, (~ (((k2_relat_1 @ sk_C_4) = (k1_tarski @ sk_B)))),
% 3.70/3.92      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 3.70/3.92  thf('88', plain, (((k2_relat_1 @ sk_C_4) != (k1_tarski @ sk_B))),
% 3.70/3.92      inference('simpl_trail', [status(thm)], ['48', '87'])).
% 3.70/3.92  thf('89', plain, ($false),
% 3.70/3.92      inference('simplify_reflect-', [status(thm)], ['46', '88'])).
% 3.70/3.92  
% 3.70/3.92  % SZS output end Refutation
% 3.70/3.92  
% 3.70/3.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
