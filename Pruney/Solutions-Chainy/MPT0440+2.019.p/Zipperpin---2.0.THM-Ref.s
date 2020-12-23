%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yo4OkKeN7a

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:44 EST 2020

% Result     : Theorem 32.97s
% Output     : Refutation 32.97s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 425 expanded)
%              Number of leaves         :   21 ( 130 expanded)
%              Depth                    :   19
%              Number of atoms          :  829 (5687 expanded)
%              Number of equality atoms :   79 ( 467 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X15 ) ) )
      | ( X13 != X15 )
      | ( X12 != X11 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('2',plain,(
    ! [X11: $i,X15: $i] :
      ( r2_hidden @ ( k4_tarski @ X11 @ X15 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('4',plain,(
    ! [X11: $i,X15: $i] :
      ( r2_hidden @ ( k4_tarski @ X11 @ X15 ) @ ( k1_tarski @ ( k4_tarski @ X11 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ),
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
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8 = X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('14',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_relat_1 @ X0 ) @ sk_C_2 )
        = sk_B )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k1_relat_1 @ X0 ) @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ ( k1_relat_1 @ X0 ) @ sk_C_2 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k1_tarski @ ( k4_tarski @ X11 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ sk_C_2 )
        = sk_B )
      | ( ( sk_C_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ sk_C_2 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ ( k1_tarski @ X10 ) ) )
      | ( X8 != X10 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X10 ) @ ( k2_zfmisc_1 @ X7 @ ( k1_tarski @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ X2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ X24 ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('38',plain,(
    ! [X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X1 ) @ sk_C_2 )
        = sk_B )
      | ( ( sk_C_1 @ ( k1_tarski @ X1 ) @ sk_C_2 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['19','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(eq_fact,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('50',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['42','50'])).

thf('52',plain,
    ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['40','51'])).

thf('56',plain,(
    ! [X11: $i,X15: $i] :
      ( r2_hidden @ ( k4_tarski @ X11 @ X15 ) @ ( k1_tarski @ ( k4_tarski @ X11 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('58',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_2 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['54','55','58'])).

thf('60',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['42','50'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('sup-',[status(thm)],['5','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yo4OkKeN7a
% 0.14/0.36  % Computer   : n017.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:38:02 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 32.97/33.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 32.97/33.13  % Solved by: fo/fo7.sh
% 32.97/33.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.97/33.13  % done 7840 iterations in 32.684s
% 32.97/33.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 32.97/33.13  % SZS output start Refutation
% 32.97/33.13  thf(sk_A_type, type, sk_A: $i).
% 32.97/33.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 32.97/33.13  thf(sk_C_2_type, type, sk_C_2: $i).
% 32.97/33.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 32.97/33.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 32.97/33.13  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 32.97/33.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 32.97/33.13  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 32.97/33.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 32.97/33.13  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 32.97/33.13  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 32.97/33.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.97/33.13  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 32.97/33.13  thf(sk_B_type, type, sk_B: $i).
% 32.97/33.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 32.97/33.13  thf(t23_relat_1, conjecture,
% 32.97/33.13    (![A:$i,B:$i,C:$i]:
% 32.97/33.13     ( ( v1_relat_1 @ C ) =>
% 32.97/33.13       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 32.97/33.13         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 32.97/33.13           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 32.97/33.13  thf(zf_stmt_0, negated_conjecture,
% 32.97/33.13    (~( ![A:$i,B:$i,C:$i]:
% 32.97/33.13        ( ( v1_relat_1 @ C ) =>
% 32.97/33.13          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 32.97/33.13            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 32.97/33.13              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 32.97/33.13    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 32.97/33.13  thf('0', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 32.97/33.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.97/33.13  thf(t34_zfmisc_1, axiom,
% 32.97/33.13    (![A:$i,B:$i,C:$i,D:$i]:
% 32.97/33.13     ( ( r2_hidden @
% 32.97/33.13         ( k4_tarski @ A @ B ) @ 
% 32.97/33.13         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 32.97/33.13       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 32.97/33.13  thf('1', plain,
% 32.97/33.13      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 32.97/33.13         ((r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 32.97/33.13           (k2_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X15)))
% 32.97/33.13          | ((X13) != (X15))
% 32.97/33.13          | ((X12) != (X11)))),
% 32.97/33.13      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 32.97/33.13  thf('2', plain,
% 32.97/33.13      (![X11 : $i, X15 : $i]:
% 32.97/33.13         (r2_hidden @ (k4_tarski @ X11 @ X15) @ 
% 32.97/33.13          (k2_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X15)))),
% 32.97/33.13      inference('simplify', [status(thm)], ['1'])).
% 32.97/33.13  thf(t35_zfmisc_1, axiom,
% 32.97/33.13    (![A:$i,B:$i]:
% 32.97/33.13     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 32.97/33.13       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 32.97/33.13  thf('3', plain,
% 32.97/33.13      (![X16 : $i, X17 : $i]:
% 32.97/33.13         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 32.97/33.13           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 32.97/33.13      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 32.97/33.13  thf('4', plain,
% 32.97/33.13      (![X11 : $i, X15 : $i]:
% 32.97/33.13         (r2_hidden @ (k4_tarski @ X11 @ X15) @ 
% 32.97/33.13          (k1_tarski @ (k4_tarski @ X11 @ X15)))),
% 32.97/33.13      inference('demod', [status(thm)], ['2', '3'])).
% 32.97/33.13  thf('5', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)),
% 32.97/33.13      inference('sup+', [status(thm)], ['0', '4'])).
% 32.97/33.13  thf(d5_relat_1, axiom,
% 32.97/33.13    (![A:$i,B:$i]:
% 32.97/33.13     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 32.97/33.13       ( ![C:$i]:
% 32.97/33.13         ( ( r2_hidden @ C @ B ) <=>
% 32.97/33.13           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 32.97/33.13  thf('6', plain,
% 32.97/33.13      (![X27 : $i, X30 : $i]:
% 32.97/33.13         (((X30) = (k2_relat_1 @ X27))
% 32.97/33.13          | (r2_hidden @ 
% 32.97/33.13             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_1 @ X30 @ X27)) @ X27)
% 32.97/33.13          | (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 32.97/33.13      inference('cnf', [status(esa)], [d5_relat_1])).
% 32.97/33.13  thf('7', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 32.97/33.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.97/33.13  thf('8', plain,
% 32.97/33.13      (![X16 : $i, X17 : $i]:
% 32.97/33.13         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 32.97/33.13           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 32.97/33.13      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 32.97/33.13  thf(t129_zfmisc_1, axiom,
% 32.97/33.13    (![A:$i,B:$i,C:$i,D:$i]:
% 32.97/33.13     ( ( r2_hidden @
% 32.97/33.13         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 32.97/33.13       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 32.97/33.13  thf('9', plain,
% 32.97/33.13      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 32.97/33.13         (((X8) = (X9))
% 32.97/33.13          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 32.97/33.13               (k2_zfmisc_1 @ X7 @ (k1_tarski @ X9))))),
% 32.97/33.13      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 32.97/33.13  thf('10', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.97/33.13         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 32.97/33.13             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 32.97/33.13          | ((X2) = (X0)))),
% 32.97/33.13      inference('sup-', [status(thm)], ['8', '9'])).
% 32.97/33.13  thf('11', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2) | ((X0) = (sk_B)))),
% 32.97/33.13      inference('sup-', [status(thm)], ['7', '10'])).
% 32.97/33.13  thf('12', plain,
% 32.97/33.13      (![X0 : $i]:
% 32.97/33.13         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 32.97/33.13          | ((X0) = (k2_relat_1 @ sk_C_2))
% 32.97/33.13          | ((sk_C_1 @ X0 @ sk_C_2) = (sk_B)))),
% 32.97/33.13      inference('sup-', [status(thm)], ['6', '11'])).
% 32.97/33.13  thf(d4_relat_1, axiom,
% 32.97/33.13    (![A:$i,B:$i]:
% 32.97/33.13     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 32.97/33.13       ( ![C:$i]:
% 32.97/33.13         ( ( r2_hidden @ C @ B ) <=>
% 32.97/33.13           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 32.97/33.13  thf('13', plain,
% 32.97/33.13      (![X20 : $i, X21 : $i, X22 : $i]:
% 32.97/33.13         (~ (r2_hidden @ X22 @ X21)
% 32.97/33.13          | (r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 32.97/33.13          | ((X21) != (k1_relat_1 @ X20)))),
% 32.97/33.13      inference('cnf', [status(esa)], [d4_relat_1])).
% 32.97/33.13  thf('14', plain,
% 32.97/33.13      (![X20 : $i, X22 : $i]:
% 32.97/33.13         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 32.97/33.13          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 32.97/33.13      inference('simplify', [status(thm)], ['13'])).
% 32.97/33.13  thf('15', plain,
% 32.97/33.13      (![X0 : $i]:
% 32.97/33.13         (((sk_C_1 @ (k1_relat_1 @ X0) @ sk_C_2) = (sk_B))
% 32.97/33.13          | ((k1_relat_1 @ X0) = (k2_relat_1 @ sk_C_2))
% 32.97/33.13          | (r2_hidden @ 
% 32.97/33.13             (k4_tarski @ (sk_C_1 @ (k1_relat_1 @ X0) @ sk_C_2) @ 
% 32.97/33.13              (sk_D_1 @ (sk_C_1 @ (k1_relat_1 @ X0) @ sk_C_2) @ X0)) @ 
% 32.97/33.13             X0))),
% 32.97/33.13      inference('sup-', [status(thm)], ['12', '14'])).
% 32.97/33.13  thf('16', plain,
% 32.97/33.13      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 32.97/33.13         (((X12) = (X11))
% 32.97/33.13          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 32.97/33.13               (k2_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X14))))),
% 32.97/33.13      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 32.97/33.13  thf('17', plain,
% 32.97/33.13      (![X16 : $i, X17 : $i]:
% 32.97/33.13         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 32.97/33.13           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 32.97/33.13      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 32.97/33.13  thf('18', plain,
% 32.97/33.13      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 32.97/33.13         (((X12) = (X11))
% 32.97/33.13          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 32.97/33.13               (k1_tarski @ (k4_tarski @ X11 @ X14))))),
% 32.97/33.13      inference('demod', [status(thm)], ['16', '17'])).
% 32.97/33.13  thf('19', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 32.97/33.13            = (k2_relat_1 @ sk_C_2))
% 32.97/33.13          | ((sk_C_1 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 32.97/33.13              sk_C_2) = (sk_B))
% 32.97/33.13          | ((sk_C_1 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 32.97/33.13              sk_C_2) = (X1)))),
% 32.97/33.13      inference('sup-', [status(thm)], ['15', '18'])).
% 32.97/33.13  thf('20', plain,
% 32.97/33.13      (![X20 : $i, X23 : $i]:
% 32.97/33.13         (((X23) = (k1_relat_1 @ X20))
% 32.97/33.13          | (r2_hidden @ 
% 32.97/33.13             (k4_tarski @ (sk_C @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 32.97/33.13          | (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 32.97/33.13      inference('cnf', [status(esa)], [d4_relat_1])).
% 32.97/33.13  thf('21', plain,
% 32.97/33.13      (![X16 : $i, X17 : $i]:
% 32.97/33.13         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 32.97/33.13           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 32.97/33.13      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 32.97/33.13  thf('22', plain,
% 32.97/33.13      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 32.97/33.13         ((r2_hidden @ X6 @ X7)
% 32.97/33.13          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 32.97/33.13               (k2_zfmisc_1 @ X7 @ (k1_tarski @ X9))))),
% 32.97/33.13      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 32.97/33.13  thf('23', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.97/33.13         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 32.97/33.13             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 32.97/33.13          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 32.97/33.13      inference('sup-', [status(thm)], ['21', '22'])).
% 32.97/33.13  thf('24', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.97/33.13         ((r2_hidden @ (sk_C @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 32.97/33.13          | ((X2) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 32.97/33.13          | (r2_hidden @ (sk_C @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 32.97/33.13             (k1_tarski @ X1)))),
% 32.97/33.13      inference('sup-', [status(thm)], ['20', '23'])).
% 32.97/33.13  thf('25', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         ((r2_hidden @ 
% 32.97/33.13           (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 32.97/33.13           (k1_tarski @ X0))
% 32.97/33.13          | ((k1_tarski @ X0)
% 32.97/33.13              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 32.97/33.13      inference('eq_fact', [status(thm)], ['24'])).
% 32.97/33.13  thf('26', plain,
% 32.97/33.13      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 32.97/33.13         ((r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 32.97/33.13           (k2_zfmisc_1 @ X7 @ (k1_tarski @ X10)))
% 32.97/33.13          | ((X8) != (X10))
% 32.97/33.13          | ~ (r2_hidden @ X6 @ X7))),
% 32.97/33.13      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 32.97/33.13  thf('27', plain,
% 32.97/33.13      (![X6 : $i, X7 : $i, X10 : $i]:
% 32.97/33.13         (~ (r2_hidden @ X6 @ X7)
% 32.97/33.13          | (r2_hidden @ (k4_tarski @ X6 @ X10) @ 
% 32.97/33.13             (k2_zfmisc_1 @ X7 @ (k1_tarski @ X10))))),
% 32.97/33.13      inference('simplify', [status(thm)], ['26'])).
% 32.97/33.13  thf('28', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.97/33.13         (((k1_tarski @ X0)
% 32.97/33.13            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 32.97/33.13          | (r2_hidden @ 
% 32.97/33.13             (k4_tarski @ 
% 32.97/33.13              (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 32.97/33.13              X2) @ 
% 32.97/33.13             (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X2))))),
% 32.97/33.13      inference('sup-', [status(thm)], ['25', '27'])).
% 32.97/33.13  thf('29', plain,
% 32.97/33.13      (![X16 : $i, X17 : $i]:
% 32.97/33.13         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 32.97/33.13           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 32.97/33.13      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 32.97/33.13  thf('30', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.97/33.13         (((k1_tarski @ X0)
% 32.97/33.13            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 32.97/33.13          | (r2_hidden @ 
% 32.97/33.13             (k4_tarski @ 
% 32.97/33.13              (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 32.97/33.13              X2) @ 
% 32.97/33.13             (k1_tarski @ (k4_tarski @ X0 @ X2))))),
% 32.97/33.13      inference('demod', [status(thm)], ['28', '29'])).
% 32.97/33.13  thf('31', plain,
% 32.97/33.13      (![X20 : $i, X23 : $i, X24 : $i]:
% 32.97/33.13         (((X23) = (k1_relat_1 @ X20))
% 32.97/33.13          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X23 @ X20) @ X24) @ X20)
% 32.97/33.13          | ~ (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 32.97/33.13      inference('cnf', [status(esa)], [d4_relat_1])).
% 32.97/33.13  thf('32', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         (((k1_tarski @ X1)
% 32.97/33.13            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 32.97/33.13          | ~ (r2_hidden @ 
% 32.97/33.13               (sk_C @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 32.97/33.13               (k1_tarski @ X1))
% 32.97/33.13          | ((k1_tarski @ X1)
% 32.97/33.13              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 32.97/33.13      inference('sup-', [status(thm)], ['30', '31'])).
% 32.97/33.13  thf('33', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         (~ (r2_hidden @ 
% 32.97/33.13             (sk_C @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 32.97/33.13             (k1_tarski @ X1))
% 32.97/33.13          | ((k1_tarski @ X1)
% 32.97/33.13              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 32.97/33.13      inference('simplify', [status(thm)], ['32'])).
% 32.97/33.13  thf('34', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         ((r2_hidden @ 
% 32.97/33.13           (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 32.97/33.13           (k1_tarski @ X0))
% 32.97/33.13          | ((k1_tarski @ X0)
% 32.97/33.13              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 32.97/33.13      inference('eq_fact', [status(thm)], ['24'])).
% 32.97/33.13  thf('35', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 32.97/33.13      inference('clc', [status(thm)], ['33', '34'])).
% 32.97/33.13  thf('36', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 32.97/33.13      inference('clc', [status(thm)], ['33', '34'])).
% 32.97/33.13  thf('37', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 32.97/33.13      inference('clc', [status(thm)], ['33', '34'])).
% 32.97/33.13  thf('38', plain,
% 32.97/33.13      (![X1 : $i]:
% 32.97/33.13         (((k1_tarski @ X1) = (k2_relat_1 @ sk_C_2))
% 32.97/33.13          | ((sk_C_1 @ (k1_tarski @ X1) @ sk_C_2) = (sk_B))
% 32.97/33.13          | ((sk_C_1 @ (k1_tarski @ X1) @ sk_C_2) = (X1)))),
% 32.97/33.13      inference('demod', [status(thm)], ['19', '35', '36', '37'])).
% 32.97/33.13  thf('39', plain,
% 32.97/33.13      (![X0 : $i]:
% 32.97/33.13         (((X0) != (sk_B))
% 32.97/33.13          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_2) = (sk_B))
% 32.97/33.13          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2)))),
% 32.97/33.13      inference('eq_fact', [status(thm)], ['38'])).
% 32.97/33.13  thf('40', plain,
% 32.97/33.13      ((((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))
% 32.97/33.13        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) = (sk_B)))),
% 32.97/33.13      inference('simplify', [status(thm)], ['39'])).
% 32.97/33.13  thf('41', plain,
% 32.97/33.13      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A))
% 32.97/33.13        | ((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B)))),
% 32.97/33.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.97/33.13  thf('42', plain,
% 32.97/33.13      ((((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B)))
% 32.97/33.13         <= (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B))))),
% 32.97/33.13      inference('split', [status(esa)], ['41'])).
% 32.97/33.13  thf('43', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 32.97/33.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.97/33.13  thf('44', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i]:
% 32.97/33.13         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 32.97/33.13      inference('clc', [status(thm)], ['33', '34'])).
% 32.97/33.13  thf('45', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 32.97/33.13      inference('sup+', [status(thm)], ['43', '44'])).
% 32.97/33.13  thf('46', plain,
% 32.97/33.13      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A)))
% 32.97/33.13         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 32.97/33.13      inference('split', [status(esa)], ['41'])).
% 32.97/33.13  thf('47', plain,
% 32.97/33.13      ((((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_C_2)))
% 32.97/33.13         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 32.97/33.13      inference('sup-', [status(thm)], ['45', '46'])).
% 32.97/33.13  thf('48', plain, ((((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A)))),
% 32.97/33.13      inference('simplify', [status(thm)], ['47'])).
% 32.97/33.13  thf('49', plain,
% 32.97/33.13      (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B))) | 
% 32.97/33.13       ~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A)))),
% 32.97/33.13      inference('split', [status(esa)], ['41'])).
% 32.97/33.13  thf('50', plain, (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B)))),
% 32.97/33.13      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 32.97/33.13  thf('51', plain, (((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B))),
% 32.97/33.13      inference('simpl_trail', [status(thm)], ['42', '50'])).
% 32.97/33.13  thf('52', plain, (((sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) = (sk_B))),
% 32.97/33.13      inference('simplify_reflect-', [status(thm)], ['40', '51'])).
% 32.97/33.13  thf('53', plain,
% 32.97/33.13      (![X27 : $i, X30 : $i, X31 : $i]:
% 32.97/33.13         (((X30) = (k2_relat_1 @ X27))
% 32.97/33.13          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_1 @ X30 @ X27)) @ X27)
% 32.97/33.13          | ~ (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 32.97/33.13      inference('cnf', [status(esa)], [d5_relat_1])).
% 32.97/33.13  thf('54', plain,
% 32.97/33.13      (![X0 : $i]:
% 32.97/33.13         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_2)
% 32.97/33.13          | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) @ 
% 32.97/33.13               (k1_tarski @ sk_B))
% 32.97/33.13          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2)))),
% 32.97/33.13      inference('sup-', [status(thm)], ['52', '53'])).
% 32.97/33.13  thf('55', plain, (((sk_C_1 @ (k1_tarski @ sk_B) @ sk_C_2) = (sk_B))),
% 32.97/33.13      inference('simplify_reflect-', [status(thm)], ['40', '51'])).
% 32.97/33.13  thf('56', plain,
% 32.97/33.13      (![X11 : $i, X15 : $i]:
% 32.97/33.13         (r2_hidden @ (k4_tarski @ X11 @ X15) @ 
% 32.97/33.13          (k1_tarski @ (k4_tarski @ X11 @ X15)))),
% 32.97/33.13      inference('demod', [status(thm)], ['2', '3'])).
% 32.97/33.13  thf('57', plain,
% 32.97/33.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.97/33.13         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 32.97/33.13             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 32.97/33.13          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 32.97/33.13      inference('sup-', [status(thm)], ['21', '22'])).
% 32.97/33.13  thf('58', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 32.97/33.13      inference('sup-', [status(thm)], ['56', '57'])).
% 32.97/33.13  thf('59', plain,
% 32.97/33.13      (![X0 : $i]:
% 32.97/33.13         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_2)
% 32.97/33.13          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2)))),
% 32.97/33.13      inference('demod', [status(thm)], ['54', '55', '58'])).
% 32.97/33.13  thf('60', plain, (((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B))),
% 32.97/33.13      inference('simpl_trail', [status(thm)], ['42', '50'])).
% 32.97/33.13  thf('61', plain,
% 32.97/33.13      (![X0 : $i]: ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_2)),
% 32.97/33.13      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 32.97/33.13  thf('62', plain, ($false), inference('sup-', [status(thm)], ['5', '61'])).
% 32.97/33.13  
% 32.97/33.13  % SZS output end Refutation
% 32.97/33.13  
% 32.97/33.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
