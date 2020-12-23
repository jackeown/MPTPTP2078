%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aejttGq9OE

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:43 EST 2020

% Result     : Theorem 11.20s
% Output     : Refutation 11.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 302 expanded)
%              Number of leaves         :   23 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          :  946 (3371 expanded)
%              Number of equality atoms :   95 ( 405 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('1',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
      = ( k1_tarski @ ( k4_tarski @ X0 @ ( k4_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('10',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ X1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D_1 @ X1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('22',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_2 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_2 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_C_2 @ X30 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ ( k1_tarski @ ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf('36',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('38',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('40',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_3 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_3 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('51',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ X24 ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['38','57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','60'])).

thf('62',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('64',plain,
    ( sk_C_3
    = ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( sk_C_3
      = ( k1_tarski @ ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) ) ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['34','65'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['38','57'])).

thf('70',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['67'])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['67'])).

thf('74',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['68','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aejttGq9OE
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 11.20/11.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.20/11.39  % Solved by: fo/fo7.sh
% 11.20/11.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.20/11.39  % done 4653 iterations in 10.920s
% 11.20/11.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.20/11.39  % SZS output start Refutation
% 11.20/11.39  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 11.20/11.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.20/11.39  thf(sk_B_type, type, sk_B: $i).
% 11.20/11.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 11.20/11.39  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 11.20/11.39  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 11.20/11.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.20/11.39  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 11.20/11.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.20/11.39  thf(sk_A_type, type, sk_A: $i).
% 11.20/11.39  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 11.20/11.39  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.20/11.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.20/11.39  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 11.20/11.39  thf(sk_C_3_type, type, sk_C_3: $i).
% 11.20/11.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 11.20/11.39  thf(t69_enumset1, axiom,
% 11.20/11.39    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 11.20/11.39  thf('0', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 11.20/11.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 11.20/11.39  thf(t23_relat_1, conjecture,
% 11.20/11.39    (![A:$i,B:$i,C:$i]:
% 11.20/11.39     ( ( v1_relat_1 @ C ) =>
% 11.20/11.39       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 11.20/11.39         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 11.20/11.39           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 11.20/11.39  thf(zf_stmt_0, negated_conjecture,
% 11.20/11.39    (~( ![A:$i,B:$i,C:$i]:
% 11.20/11.39        ( ( v1_relat_1 @ C ) =>
% 11.20/11.39          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 11.20/11.39            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 11.20/11.39              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 11.20/11.39    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 11.20/11.39  thf('1', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.20/11.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.20/11.39  thf(t35_zfmisc_1, axiom,
% 11.20/11.39    (![A:$i,B:$i]:
% 11.20/11.39     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 11.20/11.39       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 11.20/11.39  thf('2', plain,
% 11.20/11.39      (![X16 : $i, X17 : $i]:
% 11.20/11.39         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 11.20/11.39           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 11.20/11.39      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 11.20/11.39  thf('3', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C_3)
% 11.20/11.39           = (k1_tarski @ (k4_tarski @ X0 @ (k4_tarski @ sk_A @ sk_B))))),
% 11.20/11.39      inference('sup+', [status(thm)], ['1', '2'])).
% 11.20/11.39  thf(d1_tarski, axiom,
% 11.20/11.39    (![A:$i,B:$i]:
% 11.20/11.39     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 11.20/11.39       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 11.20/11.39  thf('4', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.20/11.39         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 11.20/11.39      inference('cnf', [status(esa)], [d1_tarski])).
% 11.20/11.39  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 11.20/11.39      inference('simplify', [status(thm)], ['4'])).
% 11.20/11.39  thf(d4_relat_1, axiom,
% 11.20/11.39    (![A:$i,B:$i]:
% 11.20/11.39     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 11.20/11.39       ( ![C:$i]:
% 11.20/11.39         ( ( r2_hidden @ C @ B ) <=>
% 11.20/11.39           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 11.20/11.39  thf('6', plain,
% 11.20/11.39      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 11.20/11.39          | (r2_hidden @ X18 @ X21)
% 11.20/11.39          | ((X21) != (k1_relat_1 @ X20)))),
% 11.20/11.39      inference('cnf', [status(esa)], [d4_relat_1])).
% 11.20/11.39  thf('7', plain,
% 11.20/11.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 11.20/11.39         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 11.20/11.39      inference('simplify', [status(thm)], ['6'])).
% 11.20/11.39  thf('8', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (r2_hidden @ X1 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 11.20/11.39      inference('sup-', [status(thm)], ['5', '7'])).
% 11.20/11.39  thf('9', plain,
% 11.20/11.39      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.20/11.39         (~ (r2_hidden @ X22 @ X21)
% 11.20/11.39          | (r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 11.20/11.39          | ((X21) != (k1_relat_1 @ X20)))),
% 11.20/11.39      inference('cnf', [status(esa)], [d4_relat_1])).
% 11.20/11.39  thf('10', plain,
% 11.20/11.39      (![X20 : $i, X22 : $i]:
% 11.20/11.39         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 11.20/11.39          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['9'])).
% 11.20/11.39  thf('11', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (r2_hidden @ 
% 11.20/11.39          (k4_tarski @ X1 @ (sk_D_1 @ X1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 11.20/11.39          (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['8', '10'])).
% 11.20/11.39  thf('12', plain,
% 11.20/11.39      (![X16 : $i, X17 : $i]:
% 11.20/11.39         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 11.20/11.39           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 11.20/11.39      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 11.20/11.39  thf(t128_zfmisc_1, axiom,
% 11.20/11.39    (![A:$i,B:$i,C:$i,D:$i]:
% 11.20/11.39     ( ( r2_hidden @
% 11.20/11.39         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 11.20/11.39       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 11.20/11.39  thf('13', plain,
% 11.20/11.39      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 11.20/11.39         ((r2_hidden @ X13 @ X14)
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 11.20/11.39               (k2_zfmisc_1 @ (k1_tarski @ X11) @ X14)))),
% 11.20/11.39      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 11.20/11.39  thf('14', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 11.20/11.39             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 11.20/11.39          | (r2_hidden @ X2 @ (k1_tarski @ X0)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['12', '13'])).
% 11.20/11.39  thf('15', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 11.20/11.39          (k1_tarski @ X0))),
% 11.20/11.39      inference('sup-', [status(thm)], ['11', '14'])).
% 11.20/11.39  thf('16', plain,
% 11.20/11.39      (![X0 : $i, X2 : $i, X3 : $i]:
% 11.20/11.39         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 11.20/11.39      inference('cnf', [status(esa)], [d1_tarski])).
% 11.20/11.39  thf('17', plain,
% 11.20/11.39      (![X0 : $i, X3 : $i]:
% 11.20/11.39         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['16'])).
% 11.20/11.39  thf('18', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         ((sk_D_1 @ X1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (X0))),
% 11.20/11.39      inference('sup-', [status(thm)], ['15', '17'])).
% 11.20/11.39  thf('19', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C_3))
% 11.20/11.39           = (k4_tarski @ sk_A @ sk_B))),
% 11.20/11.39      inference('sup+', [status(thm)], ['3', '18'])).
% 11.20/11.39  thf('20', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3))
% 11.20/11.39           = (k4_tarski @ sk_A @ sk_B))),
% 11.20/11.39      inference('sup+', [status(thm)], ['0', '19'])).
% 11.20/11.39  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 11.20/11.39      inference('simplify', [status(thm)], ['4'])).
% 11.20/11.39  thf(d5_relat_1, axiom,
% 11.20/11.39    (![A:$i,B:$i]:
% 11.20/11.39     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 11.20/11.39       ( ![C:$i]:
% 11.20/11.39         ( ( r2_hidden @ C @ B ) <=>
% 11.20/11.39           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 11.20/11.39  thf('22', plain,
% 11.20/11.39      (![X27 : $i, X30 : $i]:
% 11.20/11.39         (((X30) = (k2_relat_1 @ X27))
% 11.20/11.39          | (r2_hidden @ 
% 11.20/11.39             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_2 @ X30 @ X27)) @ X27)
% 11.20/11.39          | (r2_hidden @ (sk_C_2 @ X30 @ X27) @ X30))),
% 11.20/11.39      inference('cnf', [status(esa)], [d5_relat_1])).
% 11.20/11.39  thf('23', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 11.20/11.39             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 11.20/11.39          | (r2_hidden @ X2 @ (k1_tarski @ X0)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['12', '13'])).
% 11.20/11.39  thf('24', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.20/11.39         ((r2_hidden @ (sk_C_2 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 11.20/11.39          | ((X2) = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 11.20/11.39          | (r2_hidden @ (sk_C_2 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 11.20/11.39             (k1_tarski @ X0)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['22', '23'])).
% 11.20/11.39  thf('25', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         ((r2_hidden @ 
% 11.20/11.39           (sk_C_2 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 11.20/11.39           (k1_tarski @ X0))
% 11.20/11.39          | ((k1_tarski @ X0)
% 11.20/11.39              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 11.20/11.39      inference('eq_fact', [status(thm)], ['24'])).
% 11.20/11.39  thf('26', plain,
% 11.20/11.39      (![X0 : $i, X3 : $i]:
% 11.20/11.39         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['16'])).
% 11.20/11.39  thf('27', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (((k1_tarski @ X0)
% 11.20/11.39            = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 11.20/11.39          | ((sk_C_2 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 11.20/11.39              = (X0)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['25', '26'])).
% 11.20/11.39  thf('28', plain,
% 11.20/11.39      (![X27 : $i, X30 : $i, X31 : $i]:
% 11.20/11.39         (((X30) = (k2_relat_1 @ X27))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_2 @ X30 @ X27)) @ X27)
% 11.20/11.39          | ~ (r2_hidden @ (sk_C_2 @ X30 @ X27) @ X30))),
% 11.20/11.39      inference('cnf', [status(esa)], [d5_relat_1])).
% 11.20/11.39  thf('29', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 11.20/11.39             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 11.20/11.39          | ((k1_tarski @ X0)
% 11.20/11.39              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 11.20/11.39          | ~ (r2_hidden @ 
% 11.20/11.39               (sk_C_2 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 11.20/11.39               (k1_tarski @ X0))
% 11.20/11.39          | ((k1_tarski @ X0)
% 11.20/11.39              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 11.20/11.39      inference('sup-', [status(thm)], ['27', '28'])).
% 11.20/11.39  thf('30', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.20/11.39         (~ (r2_hidden @ 
% 11.20/11.39             (sk_C_2 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 11.20/11.39             (k1_tarski @ X0))
% 11.20/11.39          | ((k1_tarski @ X0)
% 11.20/11.39              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 11.20/11.39               (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 11.20/11.39      inference('simplify', [status(thm)], ['29'])).
% 11.20/11.39  thf('31', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         ((r2_hidden @ 
% 11.20/11.39           (sk_C_2 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 11.20/11.39           (k1_tarski @ X0))
% 11.20/11.39          | ((k1_tarski @ X0)
% 11.20/11.39              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 11.20/11.39      inference('eq_fact', [status(thm)], ['24'])).
% 11.20/11.39  thf('32', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 11.20/11.39             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 11.20/11.39          | ((k1_tarski @ X0)
% 11.20/11.39              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 11.20/11.39      inference('clc', [status(thm)], ['30', '31'])).
% 11.20/11.39  thf('33', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         ((k1_tarski @ X0) = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 11.20/11.39      inference('sup-', [status(thm)], ['21', '32'])).
% 11.20/11.39  thf('34', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((k1_tarski @ sk_B)
% 11.20/11.39           = (k2_relat_1 @ 
% 11.20/11.39              (k1_tarski @ 
% 11.20/11.39               (sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3)))))),
% 11.20/11.39      inference('sup+', [status(thm)], ['20', '33'])).
% 11.20/11.39  thf('35', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3))
% 11.20/11.39           = (k4_tarski @ sk_A @ sk_B))),
% 11.20/11.39      inference('sup+', [status(thm)], ['0', '19'])).
% 11.20/11.39  thf('36', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.20/11.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.20/11.39  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 11.20/11.39      inference('simplify', [status(thm)], ['4'])).
% 11.20/11.39  thf('38', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 11.20/11.39      inference('sup+', [status(thm)], ['36', '37'])).
% 11.20/11.39  thf('39', plain,
% 11.20/11.39      (![X20 : $i, X23 : $i]:
% 11.20/11.39         (((X23) = (k1_relat_1 @ X20))
% 11.20/11.39          | (r2_hidden @ 
% 11.20/11.39             (k4_tarski @ (sk_C_1 @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 11.20/11.39          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 11.20/11.39      inference('cnf', [status(esa)], [d4_relat_1])).
% 11.20/11.39  thf('40', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.20/11.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.20/11.39  thf('41', plain,
% 11.20/11.39      (![X16 : $i, X17 : $i]:
% 11.20/11.39         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 11.20/11.39           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 11.20/11.39      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 11.20/11.39  thf('42', plain,
% 11.20/11.39      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 11.20/11.39         (((X12) = (X11))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 11.20/11.39               (k2_zfmisc_1 @ (k1_tarski @ X11) @ X14)))),
% 11.20/11.39      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 11.20/11.39  thf('43', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 11.20/11.39             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 11.20/11.39          | ((X3) = (X1)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['41', '42'])).
% 11.20/11.39  thf('44', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X1) = (sk_A)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['40', '43'])).
% 11.20/11.39  thf('45', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X0)
% 11.20/11.39          | ((X0) = (k1_relat_1 @ sk_C_3))
% 11.20/11.39          | ((sk_C_1 @ X0 @ sk_C_3) = (sk_A)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['39', '44'])).
% 11.20/11.39  thf('46', plain,
% 11.20/11.39      (![X0 : $i, X3 : $i]:
% 11.20/11.39         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['16'])).
% 11.20/11.39  thf('47', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (sk_A))
% 11.20/11.39          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3))
% 11.20/11.39          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['45', '46'])).
% 11.20/11.39  thf('48', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (((sk_A) != (X0))
% 11.20/11.39          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0))
% 11.20/11.39          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3)))),
% 11.20/11.39      inference('eq_fact', [status(thm)], ['47'])).
% 11.20/11.39  thf('49', plain,
% 11.20/11.39      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 11.20/11.39        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['48'])).
% 11.20/11.39  thf('50', plain,
% 11.20/11.39      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 11.20/11.39        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['48'])).
% 11.20/11.39  thf('51', plain,
% 11.20/11.39      (![X20 : $i, X23 : $i, X24 : $i]:
% 11.20/11.39         (((X23) = (k1_relat_1 @ X20))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X23 @ X20) @ X24) @ X20)
% 11.20/11.39          | ~ (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 11.20/11.39      inference('cnf', [status(esa)], [d4_relat_1])).
% 11.20/11.39  thf('52', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 11.20/11.39          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 11.20/11.39          | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 11.20/11.39               (k1_tarski @ sk_A))
% 11.20/11.39          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['50', '51'])).
% 11.20/11.39  thf('53', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 11.20/11.39             (k1_tarski @ sk_A))
% 11.20/11.39          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3))),
% 11.20/11.39      inference('simplify', [status(thm)], ['52'])).
% 11.20/11.39  thf('54', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 11.20/11.39          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 11.20/11.39          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['49', '53'])).
% 11.20/11.39  thf('55', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 11.20/11.39      inference('simplify', [status(thm)], ['4'])).
% 11.20/11.39  thf('56', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 11.20/11.39          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 11.20/11.39      inference('demod', [status(thm)], ['54', '55'])).
% 11.20/11.39  thf('57', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 11.20/11.39          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['56'])).
% 11.20/11.39  thf('58', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 11.20/11.39      inference('sup-', [status(thm)], ['38', '57'])).
% 11.20/11.39  thf('59', plain,
% 11.20/11.39      (![X16 : $i, X17 : $i]:
% 11.20/11.39         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 11.20/11.39           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 11.20/11.39      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 11.20/11.39  thf('60', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ X0))
% 11.20/11.39           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 11.20/11.39      inference('sup+', [status(thm)], ['58', '59'])).
% 11.20/11.39  thf('61', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_B))
% 11.20/11.39           = (k1_tarski @ 
% 11.20/11.39              (sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3))))),
% 11.20/11.39      inference('sup+', [status(thm)], ['35', '60'])).
% 11.20/11.39  thf('62', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.20/11.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.20/11.39  thf('63', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ X0))
% 11.20/11.39           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 11.20/11.39      inference('sup+', [status(thm)], ['58', '59'])).
% 11.20/11.39  thf('64', plain,
% 11.20/11.39      (((sk_C_3) = (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ (k1_tarski @ sk_B)))),
% 11.20/11.39      inference('demod', [status(thm)], ['62', '63'])).
% 11.20/11.39  thf('65', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         ((sk_C_3)
% 11.20/11.39           = (k1_tarski @ 
% 11.20/11.39              (sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3))))),
% 11.20/11.39      inference('demod', [status(thm)], ['61', '64'])).
% 11.20/11.39  thf('66', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))),
% 11.20/11.39      inference('demod', [status(thm)], ['34', '65'])).
% 11.20/11.39  thf('67', plain,
% 11.20/11.39      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))
% 11.20/11.39        | ((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))),
% 11.20/11.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.20/11.39  thf('68', plain,
% 11.20/11.39      ((((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))
% 11.20/11.39         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 11.20/11.39      inference('split', [status(esa)], ['67'])).
% 11.20/11.39  thf('69', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 11.20/11.39      inference('sup-', [status(thm)], ['38', '57'])).
% 11.20/11.39  thf('70', plain,
% 11.20/11.39      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A)))
% 11.20/11.39         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 11.20/11.39      inference('split', [status(esa)], ['67'])).
% 11.20/11.39  thf('71', plain,
% 11.20/11.39      ((((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_C_3)))
% 11.20/11.39         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 11.20/11.39      inference('sup-', [status(thm)], ['69', '70'])).
% 11.20/11.39  thf('72', plain, ((((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['71'])).
% 11.20/11.39  thf('73', plain,
% 11.20/11.39      (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))) | 
% 11.20/11.39       ~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 11.20/11.39      inference('split', [status(esa)], ['67'])).
% 11.20/11.39  thf('74', plain, (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 11.20/11.39      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 11.20/11.39  thf('75', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 11.20/11.39      inference('simpl_trail', [status(thm)], ['68', '74'])).
% 11.20/11.39  thf('76', plain, ($false),
% 11.20/11.39      inference('simplify_reflect-', [status(thm)], ['66', '75'])).
% 11.20/11.39  
% 11.20/11.39  % SZS output end Refutation
% 11.20/11.39  
% 11.20/11.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
