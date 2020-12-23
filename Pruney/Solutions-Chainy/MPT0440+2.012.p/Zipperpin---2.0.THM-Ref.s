%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h4eLeOxhzF

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:43 EST 2020

% Result     : Theorem 3.98s
% Output     : Refutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 178 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  873 (1918 expanded)
%              Number of equality atoms :   89 ( 219 expanded)
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

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D_1 @ X1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('19',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ X24 ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ ( k1_tarski @ ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('36',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( sk_C_3
      = ( k1_tarski @ ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_C_3 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['41','42'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('44',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_2 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_2 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('45',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_3 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ X0 @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['51'])).

thf('54',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_C_2 @ X30 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['43','60'])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k2_relat_1 @ sk_C_3 ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf('66',plain,(
    ( k1_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ( k1_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['40','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h4eLeOxhzF
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.98/4.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.98/4.17  % Solved by: fo/fo7.sh
% 3.98/4.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.98/4.17  % done 2354 iterations in 3.715s
% 3.98/4.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.98/4.17  % SZS output start Refutation
% 3.98/4.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.98/4.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.98/4.17  thf(sk_B_type, type, sk_B: $i).
% 3.98/4.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.98/4.17  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 3.98/4.17  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 3.98/4.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.98/4.17  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.98/4.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.98/4.17  thf(sk_A_type, type, sk_A: $i).
% 3.98/4.17  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.98/4.17  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.98/4.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.98/4.17  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.98/4.17  thf(sk_C_3_type, type, sk_C_3: $i).
% 3.98/4.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.98/4.17  thf(t69_enumset1, axiom,
% 3.98/4.17    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.98/4.17  thf('0', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 3.98/4.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.98/4.17  thf(t23_relat_1, conjecture,
% 3.98/4.17    (![A:$i,B:$i,C:$i]:
% 3.98/4.17     ( ( v1_relat_1 @ C ) =>
% 3.98/4.17       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 3.98/4.17         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 3.98/4.17           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 3.98/4.17  thf(zf_stmt_0, negated_conjecture,
% 3.98/4.17    (~( ![A:$i,B:$i,C:$i]:
% 3.98/4.17        ( ( v1_relat_1 @ C ) =>
% 3.98/4.17          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 3.98/4.17            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 3.98/4.17              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 3.98/4.17    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 3.98/4.17  thf('1', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.98/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.17  thf(t35_zfmisc_1, axiom,
% 3.98/4.17    (![A:$i,B:$i]:
% 3.98/4.17     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 3.98/4.17       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 3.98/4.17  thf('2', plain,
% 3.98/4.17      (![X16 : $i, X17 : $i]:
% 3.98/4.17         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 3.98/4.17           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 3.98/4.17      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 3.98/4.17  thf('3', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C_3)
% 3.98/4.17           = (k1_tarski @ (k4_tarski @ X0 @ (k4_tarski @ sk_A @ sk_B))))),
% 3.98/4.17      inference('sup+', [status(thm)], ['1', '2'])).
% 3.98/4.17  thf(d1_tarski, axiom,
% 3.98/4.17    (![A:$i,B:$i]:
% 3.98/4.17     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.98/4.17       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.98/4.17  thf('4', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.98/4.17         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 3.98/4.17      inference('cnf', [status(esa)], [d1_tarski])).
% 3.98/4.17  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.98/4.17      inference('simplify', [status(thm)], ['4'])).
% 3.98/4.17  thf(d4_relat_1, axiom,
% 3.98/4.17    (![A:$i,B:$i]:
% 3.98/4.17     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.98/4.17       ( ![C:$i]:
% 3.98/4.17         ( ( r2_hidden @ C @ B ) <=>
% 3.98/4.17           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.98/4.17  thf('6', plain,
% 3.98/4.17      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 3.98/4.17          | (r2_hidden @ X18 @ X21)
% 3.98/4.17          | ((X21) != (k1_relat_1 @ X20)))),
% 3.98/4.17      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.98/4.17  thf('7', plain,
% 3.98/4.17      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.98/4.17         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 3.98/4.17      inference('simplify', [status(thm)], ['6'])).
% 3.98/4.17  thf('8', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i]:
% 3.98/4.17         (r2_hidden @ X1 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 3.98/4.17      inference('sup-', [status(thm)], ['5', '7'])).
% 3.98/4.17  thf('9', plain,
% 3.98/4.17      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.98/4.17         (~ (r2_hidden @ X22 @ X21)
% 3.98/4.17          | (r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 3.98/4.17          | ((X21) != (k1_relat_1 @ X20)))),
% 3.98/4.17      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.98/4.17  thf('10', plain,
% 3.98/4.17      (![X20 : $i, X22 : $i]:
% 3.98/4.17         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 3.98/4.17          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 3.98/4.17      inference('simplify', [status(thm)], ['9'])).
% 3.98/4.17  thf('11', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i]:
% 3.98/4.17         (r2_hidden @ 
% 3.98/4.17          (k4_tarski @ X1 @ (sk_D_1 @ X1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 3.98/4.17          (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['8', '10'])).
% 3.98/4.17  thf('12', plain,
% 3.98/4.17      (![X16 : $i, X17 : $i]:
% 3.98/4.17         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 3.98/4.17           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 3.98/4.17      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 3.98/4.17  thf(t129_zfmisc_1, axiom,
% 3.98/4.17    (![A:$i,B:$i,C:$i,D:$i]:
% 3.98/4.17     ( ( r2_hidden @
% 3.98/4.17         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 3.98/4.17       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 3.98/4.17  thf('13', plain,
% 3.98/4.17      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.98/4.17         (((X13) = (X14))
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 3.98/4.17               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 3.98/4.17      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 3.98/4.17  thf('14', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.98/4.17             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.98/4.17          | ((X2) = (X0)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['12', '13'])).
% 3.98/4.17  thf('15', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i]:
% 3.98/4.17         ((sk_D_1 @ X1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (X0))),
% 3.98/4.17      inference('sup-', [status(thm)], ['11', '14'])).
% 3.98/4.17  thf('16', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C_3))
% 3.98/4.17           = (k4_tarski @ sk_A @ sk_B))),
% 3.98/4.17      inference('sup+', [status(thm)], ['3', '15'])).
% 3.98/4.17  thf('17', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3))
% 3.98/4.17           = (k4_tarski @ sk_A @ sk_B))),
% 3.98/4.17      inference('sup+', [status(thm)], ['0', '16'])).
% 3.98/4.17  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.98/4.17      inference('simplify', [status(thm)], ['4'])).
% 3.98/4.17  thf('19', plain,
% 3.98/4.17      (![X20 : $i, X23 : $i]:
% 3.98/4.17         (((X23) = (k1_relat_1 @ X20))
% 3.98/4.17          | (r2_hidden @ 
% 3.98/4.17             (k4_tarski @ (sk_C_1 @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 3.98/4.17          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 3.98/4.17      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.98/4.17  thf('20', plain,
% 3.98/4.17      (![X16 : $i, X17 : $i]:
% 3.98/4.17         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 3.98/4.17           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 3.98/4.17      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 3.98/4.17  thf('21', plain,
% 3.98/4.17      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.98/4.17         ((r2_hidden @ X11 @ X12)
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 3.98/4.17               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 3.98/4.17      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 3.98/4.17  thf('22', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.98/4.17             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.98/4.17          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['20', '21'])).
% 3.98/4.17  thf('23', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.98/4.17         ((r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 3.98/4.17          | ((X2) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 3.98/4.17          | (r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 3.98/4.17             (k1_tarski @ X1)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['19', '22'])).
% 3.98/4.17  thf('24', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i]:
% 3.98/4.17         ((r2_hidden @ 
% 3.98/4.17           (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 3.98/4.17           (k1_tarski @ X0))
% 3.98/4.17          | ((k1_tarski @ X0)
% 3.98/4.17              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 3.98/4.17      inference('eq_fact', [status(thm)], ['23'])).
% 3.98/4.17  thf('25', plain,
% 3.98/4.17      (![X0 : $i, X2 : $i, X3 : $i]:
% 3.98/4.17         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 3.98/4.17      inference('cnf', [status(esa)], [d1_tarski])).
% 3.98/4.17  thf('26', plain,
% 3.98/4.17      (![X0 : $i, X3 : $i]:
% 3.98/4.17         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 3.98/4.17      inference('simplify', [status(thm)], ['25'])).
% 3.98/4.17  thf('27', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i]:
% 3.98/4.17         (((k1_tarski @ X0)
% 3.98/4.17            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 3.98/4.17          | ((sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 3.98/4.17              = (X0)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['24', '26'])).
% 3.98/4.17  thf('28', plain,
% 3.98/4.17      (![X20 : $i, X23 : $i, X24 : $i]:
% 3.98/4.17         (((X23) = (k1_relat_1 @ X20))
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X23 @ X20) @ X24) @ X20)
% 3.98/4.17          | ~ (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 3.98/4.17      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.98/4.17  thf('29', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 3.98/4.17             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 3.98/4.17          | ((k1_tarski @ X0)
% 3.98/4.17              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 3.98/4.17          | ~ (r2_hidden @ 
% 3.98/4.17               (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 3.98/4.17               (k1_tarski @ X0))
% 3.98/4.17          | ((k1_tarski @ X0)
% 3.98/4.17              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 3.98/4.17      inference('sup-', [status(thm)], ['27', '28'])).
% 3.98/4.17  thf('30', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.98/4.17         (~ (r2_hidden @ 
% 3.98/4.17             (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 3.98/4.17             (k1_tarski @ X0))
% 3.98/4.17          | ((k1_tarski @ X0)
% 3.98/4.17              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 3.98/4.17               (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 3.98/4.17      inference('simplify', [status(thm)], ['29'])).
% 3.98/4.17  thf('31', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i]:
% 3.98/4.17         ((r2_hidden @ 
% 3.98/4.17           (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 3.98/4.17           (k1_tarski @ X0))
% 3.98/4.17          | ((k1_tarski @ X0)
% 3.98/4.17              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 3.98/4.17      inference('eq_fact', [status(thm)], ['23'])).
% 3.98/4.17  thf('32', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 3.98/4.17             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 3.98/4.17          | ((k1_tarski @ X0)
% 3.98/4.17              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 3.98/4.17      inference('clc', [status(thm)], ['30', '31'])).
% 3.98/4.17  thf('33', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i]:
% 3.98/4.17         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 3.98/4.17      inference('sup-', [status(thm)], ['18', '32'])).
% 3.98/4.17  thf('34', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         ((k1_tarski @ sk_A)
% 3.98/4.17           = (k1_relat_1 @ 
% 3.98/4.17              (k1_tarski @ 
% 3.98/4.17               (sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3)))))),
% 3.98/4.17      inference('sup+', [status(thm)], ['17', '33'])).
% 3.98/4.17  thf('35', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3))
% 3.98/4.17           = (k4_tarski @ sk_A @ sk_B))),
% 3.98/4.17      inference('sup+', [status(thm)], ['0', '16'])).
% 3.98/4.17  thf('36', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.98/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.17  thf('37', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         ((sk_C_3)
% 3.98/4.17           = (k1_tarski @ 
% 3.98/4.17              (sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_C_3))))),
% 3.98/4.17      inference('sup+', [status(thm)], ['35', '36'])).
% 3.98/4.17  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 3.98/4.17      inference('demod', [status(thm)], ['34', '37'])).
% 3.98/4.17  thf('39', plain,
% 3.98/4.17      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))
% 3.98/4.17        | ((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))),
% 3.98/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.17  thf('40', plain,
% 3.98/4.17      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A)))
% 3.98/4.17         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 3.98/4.17      inference('split', [status(esa)], ['39'])).
% 3.98/4.17  thf('41', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.98/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.17  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.98/4.17      inference('simplify', [status(thm)], ['4'])).
% 3.98/4.17  thf('43', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 3.98/4.17      inference('sup+', [status(thm)], ['41', '42'])).
% 3.98/4.17  thf(d5_relat_1, axiom,
% 3.98/4.17    (![A:$i,B:$i]:
% 3.98/4.17     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.98/4.17       ( ![C:$i]:
% 3.98/4.17         ( ( r2_hidden @ C @ B ) <=>
% 3.98/4.17           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.98/4.17  thf('44', plain,
% 3.98/4.17      (![X27 : $i, X30 : $i]:
% 3.98/4.17         (((X30) = (k2_relat_1 @ X27))
% 3.98/4.17          | (r2_hidden @ 
% 3.98/4.17             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_2 @ X30 @ X27)) @ X27)
% 3.98/4.17          | (r2_hidden @ (sk_C_2 @ X30 @ X27) @ X30))),
% 3.98/4.17      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.98/4.17  thf('45', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.98/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.17  thf('46', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.98/4.17             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.98/4.17          | ((X2) = (X0)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['12', '13'])).
% 3.98/4.17  thf('47', plain,
% 3.98/4.17      (![X0 : $i, X1 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X0) = (sk_B)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['45', '46'])).
% 3.98/4.17  thf('48', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         ((r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ X0)
% 3.98/4.17          | ((X0) = (k2_relat_1 @ sk_C_3))
% 3.98/4.17          | ((sk_C_2 @ X0 @ sk_C_3) = (sk_B)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['44', '47'])).
% 3.98/4.17  thf('49', plain,
% 3.98/4.17      (![X0 : $i, X3 : $i]:
% 3.98/4.17         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 3.98/4.17      inference('simplify', [status(thm)], ['25'])).
% 3.98/4.17  thf('50', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         (((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (sk_B))
% 3.98/4.17          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 3.98/4.17          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['48', '49'])).
% 3.98/4.17  thf('51', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         (((sk_B) != (X0))
% 3.98/4.17          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0))
% 3.98/4.17          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3)))),
% 3.98/4.17      inference('eq_fact', [status(thm)], ['50'])).
% 3.98/4.17  thf('52', plain,
% 3.98/4.17      ((((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.98/4.17        | ((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B)))),
% 3.98/4.17      inference('simplify', [status(thm)], ['51'])).
% 3.98/4.17  thf('53', plain,
% 3.98/4.17      ((((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.98/4.17        | ((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B)))),
% 3.98/4.17      inference('simplify', [status(thm)], ['51'])).
% 3.98/4.17  thf('54', plain,
% 3.98/4.17      (![X27 : $i, X30 : $i, X31 : $i]:
% 3.98/4.17         (((X30) = (k2_relat_1 @ X27))
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_2 @ X30 @ X27)) @ X27)
% 3.98/4.17          | ~ (r2_hidden @ (sk_C_2 @ X30 @ X27) @ X30))),
% 3.98/4.17      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.98/4.17  thf('55', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 3.98/4.17          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.98/4.17          | ~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 3.98/4.17               (k1_tarski @ sk_B))
% 3.98/4.17          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['53', '54'])).
% 3.98/4.17  thf('56', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 3.98/4.17             (k1_tarski @ sk_B))
% 3.98/4.17          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3))),
% 3.98/4.17      inference('simplify', [status(thm)], ['55'])).
% 3.98/4.17  thf('57', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 3.98/4.17          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 3.98/4.17          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 3.98/4.17      inference('sup-', [status(thm)], ['52', '56'])).
% 3.98/4.17  thf('58', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.98/4.17      inference('simplify', [status(thm)], ['4'])).
% 3.98/4.17  thf('59', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.98/4.17          | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 3.98/4.17          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 3.98/4.17      inference('demod', [status(thm)], ['57', '58'])).
% 3.98/4.17  thf('60', plain,
% 3.98/4.17      (![X0 : $i]:
% 3.98/4.17         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 3.98/4.17          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 3.98/4.17      inference('simplify', [status(thm)], ['59'])).
% 3.98/4.17  thf('61', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))),
% 3.98/4.17      inference('sup-', [status(thm)], ['43', '60'])).
% 3.98/4.17  thf('62', plain,
% 3.98/4.17      ((((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))
% 3.98/4.17         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 3.98/4.17      inference('split', [status(esa)], ['39'])).
% 3.98/4.17  thf('63', plain,
% 3.98/4.17      ((((k2_relat_1 @ sk_C_3) != (k2_relat_1 @ sk_C_3)))
% 3.98/4.17         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 3.98/4.17      inference('sup-', [status(thm)], ['61', '62'])).
% 3.98/4.17  thf('64', plain, ((((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 3.98/4.17      inference('simplify', [status(thm)], ['63'])).
% 3.98/4.17  thf('65', plain,
% 3.98/4.17      (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))) | 
% 3.98/4.17       ~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 3.98/4.17      inference('split', [status(esa)], ['39'])).
% 3.98/4.17  thf('66', plain, (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 3.98/4.17      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 3.98/4.17  thf('67', plain, (((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))),
% 3.98/4.17      inference('simpl_trail', [status(thm)], ['40', '66'])).
% 3.98/4.17  thf('68', plain, ($false),
% 3.98/4.17      inference('simplify_reflect-', [status(thm)], ['38', '67'])).
% 3.98/4.17  
% 3.98/4.17  % SZS output end Refutation
% 3.98/4.17  
% 3.98/4.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
