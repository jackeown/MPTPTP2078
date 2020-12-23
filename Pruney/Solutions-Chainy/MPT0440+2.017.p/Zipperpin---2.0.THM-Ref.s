%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.es8MFlAyWF

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:44 EST 2020

% Result     : Theorem 56.93s
% Output     : Refutation 56.93s
% Verified   : 
% Statistics : Number of formulae       :  280 (13618 expanded)
%              Number of leaves         :   21 (3684 expanded)
%              Depth                    :   53
%              Number of atoms          : 3654 (183237 expanded)
%              Number of equality atoms :  332 (18729 expanded)
%              Maximal formula depth    :   15 (   8 average)

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

thf('1',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X3 = X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ( X7 != X6 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('10',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ sk_C_2 )
        = sk_A )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X0 @ sk_C_2 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['1','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('29',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ X24 ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('42',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_C_2 ) ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_C_2
    = ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('51',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ ( k1_tarski @ X1 ) @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('56',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_tarski @ X1 ) @ X0 ) @ ( sk_D_1 @ ( sk_C @ ( k1_tarski @ X1 ) @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( ( sk_C @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = X2 )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_tarski @ X1 ) @ X0 ) @ ( sk_D_1 @ ( sk_C @ ( k1_tarski @ X1 ) @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('63',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ X24 ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ X1 ) @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ X1 ) @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['61','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('69',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(condensation,[status(thm)],['74'])).

thf('76',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X2 ) ) ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X2 ) ) ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X2 ) ) ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('84',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ X24 ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X3 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X3 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X2 ) ) ) ) ) )
      | ( r2_hidden @ X4 @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['54','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('95',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) )
      | ( r2_hidden @ X4 @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ) ),
    inference(condensation,[status(thm)],['97'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('99',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('100',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) )
      | ( ( sk_D_2 @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_D_2 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X1 ) )
        = X2 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X1 ) ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) )
      | ( ( sk_D_2 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) )
        = X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) @ X0 )
      | ( ( sk_D_2 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) )
        = X1 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('108',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) )
      | ( ( sk_D_2 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) )
        = X1 ) ) ),
    inference(clc,[status(thm)],['106','110'])).

thf('112',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('113',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_D_2 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) )
      | ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['111','118'])).

thf('120',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('122',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('123',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) )
      | ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) )
      | ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(condensation,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['98','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ) ),
    inference(condensation,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['129'])).

thf('131',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('133',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ sk_C_2 )
        = sk_A )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X0 @ sk_C_2 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('135',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_2 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( sk_C_2
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C @ sk_C_2 @ sk_C_2 )
        = sk_A )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 )
    | ( ( sk_C @ sk_C_2 @ sk_C_2 )
      = sk_A )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['133','138'])).

thf('140',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('141',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ sk_C_2 @ sk_C_2 )
      = sk_A )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('143',plain,
    ( ( ( sk_C @ sk_C_2 @ sk_C_2 )
      = sk_A )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_C_2 ) ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('145',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ sk_C_2 @ sk_C_2 )
      = sk_A )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ sk_C_2 @ sk_C_2 )
      = sk_A )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('148',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_C_2 ) @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['145','149'])).

thf('151',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('153',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_C_2 ) ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('155',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( sk_C_2
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_2 ) )
      | ( X1
        = ( k4_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('164',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('167',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['129'])).

thf('169',plain,
    ( ( ( ( k1_relat_1 @ sk_C_2 )
       != ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2
        = ( k1_relat_1 @ sk_C_2 ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('173',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ sk_C_2 )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['170','174'])).

thf('176',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('177',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ sk_C_2 )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['129'])).

thf('179',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('180',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ sk_C_2 )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['177','180'])).

thf('182',plain,
    ( ( ( r2_hidden @ sk_A @ sk_C_2 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['132','181'])).

thf('183',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('184',plain,
    ( ( ( r2_hidden @ sk_A @ sk_C_2 )
      | ( ( k1_tarski @ sk_A )
        = sk_C_2 )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('186',plain,
    ( ( ( r2_hidden @ sk_A @ sk_C_2 )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('188',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ sk_C_2 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ sk_C_2 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k1_tarski @ ( k4_tarski @ X0 @ sk_A ) ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('192',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ sk_C_2 )
        | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 )
      | ( r2_hidden @ sk_A @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['131','192'])).

thf('194',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('195',plain,
    ( ( ( r2_hidden @ sk_A @ sk_C_2 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('197',plain,
    ( ( ( r2_hidden @ sk_A @ sk_C_2 )
      | ( r2_hidden @ sk_A @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('200',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_D_1 @ X22 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('201',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_2 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_C_2 ) ) @ sk_C_2 )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['198','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('204',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( sk_C_2
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('206',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('208',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['129'])).

thf('210',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['208','209'])).

thf('211',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['130','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ sk_C_2 )
       != ( k2_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['128','211'])).

thf('213',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ) ),
    inference(condensation,[status(thm)],['97'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('218',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ X0 ) ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['215','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('224',plain,
    ( sk_C_2
    = ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','47'])).

thf('225',plain,(
    ! [X0: $i] :
      ( sk_C_2
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X1 )
        = sk_C_2 )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['219','225'])).

thf('227',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(clc,[status(thm)],['212','226'])).

thf('228',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('229',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('230',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('232',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X1 ) ) )
        = X1 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X1 ) ) ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X1 ) ) ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('236',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('237',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('238',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['234','235','236','237','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('242',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('243',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('244',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['241','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['245'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = X0 ) ) ),
    inference(clc,[status(thm)],['240','246'])).

thf('248',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['245'])).

thf('252',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['227','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','253'])).

thf('255',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['48','254'])).

thf('256',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['130','210'])).

thf('257',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['255','256'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.es8MFlAyWF
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 56.93/57.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 56.93/57.16  % Solved by: fo/fo7.sh
% 56.93/57.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 56.93/57.16  % done 10478 iterations in 56.698s
% 56.93/57.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 56.93/57.16  % SZS output start Refutation
% 56.93/57.16  thf(sk_A_type, type, sk_A: $i).
% 56.93/57.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 56.93/57.16  thf(sk_C_2_type, type, sk_C_2: $i).
% 56.93/57.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 56.93/57.16  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 56.93/57.16  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 56.93/57.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 56.93/57.16  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 56.93/57.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 56.93/57.16  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 56.93/57.16  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 56.93/57.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 56.93/57.16  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 56.93/57.16  thf(sk_B_type, type, sk_B: $i).
% 56.93/57.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 56.93/57.16  thf(t23_relat_1, conjecture,
% 56.93/57.16    (![A:$i,B:$i,C:$i]:
% 56.93/57.16     ( ( v1_relat_1 @ C ) =>
% 56.93/57.16       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 56.93/57.16         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 56.93/57.16           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 56.93/57.16  thf(zf_stmt_0, negated_conjecture,
% 56.93/57.16    (~( ![A:$i,B:$i,C:$i]:
% 56.93/57.16        ( ( v1_relat_1 @ C ) =>
% 56.93/57.16          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 56.93/57.16            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 56.93/57.16              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 56.93/57.16    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 56.93/57.16  thf('0', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf('1', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf(d4_relat_1, axiom,
% 56.93/57.16    (![A:$i,B:$i]:
% 56.93/57.16     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 56.93/57.16       ( ![C:$i]:
% 56.93/57.16         ( ( r2_hidden @ C @ B ) <=>
% 56.93/57.16           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 56.93/57.16  thf('2', plain,
% 56.93/57.16      (![X20 : $i, X23 : $i]:
% 56.93/57.16         (((X23) = (k1_relat_1 @ X20))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_C @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 56.93/57.16          | (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 56.93/57.16      inference('cnf', [status(esa)], [d4_relat_1])).
% 56.93/57.16  thf('3', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf(t35_zfmisc_1, axiom,
% 56.93/57.16    (![A:$i,B:$i]:
% 56.93/57.16     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 56.93/57.16       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 56.93/57.16  thf('4', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf(t128_zfmisc_1, axiom,
% 56.93/57.16    (![A:$i,B:$i,C:$i,D:$i]:
% 56.93/57.16     ( ( r2_hidden @
% 56.93/57.16         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 56.93/57.16       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 56.93/57.16  thf('5', plain,
% 56.93/57.16      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 56.93/57.16         (((X7) = (X6))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 56.93/57.16               (k2_zfmisc_1 @ (k1_tarski @ X6) @ X9)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 56.93/57.16  thf('6', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | ((X3) = (X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['4', '5'])).
% 56.93/57.16  thf('7', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2) | ((X1) = (sk_A)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['3', '6'])).
% 56.93/57.16  thf('8', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ X0)
% 56.93/57.16          | ((X0) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ((sk_C @ X0 @ sk_C_2) = (sk_A)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['2', '7'])).
% 56.93/57.16  thf('9', plain,
% 56.93/57.16      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         ((r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 56.93/57.16           (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10))
% 56.93/57.16          | ~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | ((X7) != (X6)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 56.93/57.16  thf('10', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('11', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((sk_C @ X0 @ sk_C_2) = (sk_A))
% 56.93/57.16          | ((X0) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C @ X0 @ sk_C_2)) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['8', '10'])).
% 56.93/57.16  thf(t129_zfmisc_1, axiom,
% 56.93/57.16    (![A:$i,B:$i,C:$i,D:$i]:
% 56.93/57.16     ( ( r2_hidden @
% 56.93/57.16         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 56.93/57.16       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 56.93/57.16  thf('12', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         (((X13) = (X14))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('13', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((k1_tarski @ X0) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X0) @ sk_C_2) = (sk_A))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X0) @ sk_C_2) = (X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['11', '12'])).
% 56.93/57.16  thf('14', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((sk_A) != (X0))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X0) @ sk_C_2) = (X0))
% 56.93/57.16          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('eq_fact', [status(thm)], ['13'])).
% 56.93/57.16  thf('15', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['14'])).
% 56.93/57.16  thf('16', plain,
% 56.93/57.16      (![X20 : $i, X23 : $i]:
% 56.93/57.16         (((X23) = (k1_relat_1 @ X20))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_C @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 56.93/57.16          | (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 56.93/57.16      inference('cnf', [status(esa)], [d4_relat_1])).
% 56.93/57.16  thf('17', plain,
% 56.93/57.16      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 56.93/57.16          | (r2_hidden @ X18 @ X21)
% 56.93/57.16          | ((X21) != (k1_relat_1 @ X20)))),
% 56.93/57.16      inference('cnf', [status(esa)], [d4_relat_1])).
% 56.93/57.16  thf('18', plain,
% 56.93/57.16      (![X18 : $i, X19 : $i, X20 : $i]:
% 56.93/57.16         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 56.93/57.16      inference('simplify', [status(thm)], ['17'])).
% 56.93/57.16  thf('19', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 56.93/57.16          | ((X1) = (k1_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['16', '18'])).
% 56.93/57.16  thf('20', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('21', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 56.93/57.16          | ((X0) = (k1_relat_1 @ X1))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ X0 @ X1)) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['19', '20'])).
% 56.93/57.16  thf('22', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         ((r2_hidden @ X11 @ X12)
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('23', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0) = (k1_relat_1 @ X2))
% 56.93/57.16          | (r2_hidden @ (sk_C @ (k1_tarski @ X0) @ X2) @ (k1_relat_1 @ X2))
% 56.93/57.16          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['21', '22'])).
% 56.93/57.16  thf('24', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['15', '23'])).
% 56.93/57.16  thf('25', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['24'])).
% 56.93/57.16  thf('26', plain,
% 56.93/57.16      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)
% 56.93/57.16        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['1', '25'])).
% 56.93/57.16  thf('27', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['14'])).
% 56.93/57.16  thf('28', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['14'])).
% 56.93/57.16  thf('29', plain,
% 56.93/57.16      (![X20 : $i, X23 : $i, X24 : $i]:
% 56.93/57.16         (((X23) = (k1_relat_1 @ X20))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X23 @ X20) @ X24) @ X20)
% 56.93/57.16          | ~ (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 56.93/57.16      inference('cnf', [status(esa)], [d4_relat_1])).
% 56.93/57.16  thf('30', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 56.93/57.16               (k1_tarski @ sk_A))
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['28', '29'])).
% 56.93/57.16  thf('31', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 56.93/57.16             (k1_tarski @ sk_A))
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2))),
% 56.93/57.16      inference('simplify', [status(thm)], ['30'])).
% 56.93/57.16  thf('32', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['27', '31'])).
% 56.93/57.16  thf('33', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['32'])).
% 56.93/57.16  thf('34', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf('35', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('36', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         ((r2_hidden @ X11 @ X12)
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('37', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['35', '36'])).
% 56.93/57.16  thf('38', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2)
% 56.93/57.16          | (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['34', '37'])).
% 56.93/57.16  thf('39', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2))),
% 56.93/57.16      inference('clc', [status(thm)], ['33', '38'])).
% 56.93/57.16  thf('40', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('clc', [status(thm)], ['26', '39'])).
% 56.93/57.16  thf('41', plain,
% 56.93/57.16      (![X20 : $i, X21 : $i, X22 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X22 @ X21)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 56.93/57.16          | ((X21) != (k1_relat_1 @ X20)))),
% 56.93/57.16      inference('cnf', [status(esa)], [d4_relat_1])).
% 56.93/57.16  thf('42', plain,
% 56.93/57.16      (![X20 : $i, X22 : $i]:
% 56.93/57.16         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 56.93/57.16          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['41'])).
% 56.93/57.16  thf('43', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_C_2)) @ sk_C_2))),
% 56.93/57.16      inference('sup-', [status(thm)], ['40', '42'])).
% 56.93/57.16  thf('44', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2))),
% 56.93/57.16      inference('clc', [status(thm)], ['33', '38'])).
% 56.93/57.16  thf('45', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 56.93/57.16      inference('clc', [status(thm)], ['43', '44'])).
% 56.93/57.16  thf('46', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('47', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ X0))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['45', '46'])).
% 56.93/57.16  thf('48', plain,
% 56.93/57.16      (((sk_C_2) = (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ sk_B)))),
% 56.93/57.16      inference('demod', [status(thm)], ['0', '47'])).
% 56.93/57.16  thf('49', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ X0))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['45', '46'])).
% 56.93/57.16  thf('50', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0) = (k1_relat_1 @ X2))
% 56.93/57.16          | (r2_hidden @ (sk_C @ (k1_tarski @ X0) @ X2) @ (k1_relat_1 @ X2))
% 56.93/57.16          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['21', '22'])).
% 56.93/57.16  thf('51', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('52', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         ((r2_hidden @ X3 @ (k1_tarski @ X3))
% 56.93/57.16          | ((k1_tarski @ X1) = (k1_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ (k1_tarski @ X1) @ X0)) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k1_relat_1 @ X0))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['50', '51'])).
% 56.93/57.16  thf('53', plain,
% 56.93/57.16      (![X18 : $i, X19 : $i, X20 : $i]:
% 56.93/57.16         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 56.93/57.16      inference('simplify', [status(thm)], ['17'])).
% 56.93/57.16  thf('54', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (((k1_tarski @ X2) = (k1_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X3))
% 56.93/57.16          | (r2_hidden @ X1 @ 
% 56.93/57.16             (k1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_relat_1 @ X0)))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['52', '53'])).
% 56.93/57.16  thf('55', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 56.93/57.16          | ((X0) = (k1_relat_1 @ X1))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ X0 @ X1)) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['19', '20'])).
% 56.93/57.16  thf('56', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         (((X13) = (X14))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('57', plain,
% 56.93/57.16      (![X0 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0) = (k1_relat_1 @ X2))
% 56.93/57.16          | (r2_hidden @ (sk_C @ (k1_tarski @ X0) @ X2) @ (k1_relat_1 @ X2))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X0) @ X2) = (X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['55', '56'])).
% 56.93/57.16  thf('58', plain,
% 56.93/57.16      (![X20 : $i, X22 : $i]:
% 56.93/57.16         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 56.93/57.16          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['41'])).
% 56.93/57.16  thf('59', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((sk_C @ (k1_tarski @ X1) @ X0) = (X1))
% 56.93/57.16          | ((k1_tarski @ X1) = (k1_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_C @ (k1_tarski @ X1) @ X0) @ 
% 56.93/57.16              (sk_D_1 @ (sk_C @ (k1_tarski @ X1) @ X0) @ X0)) @ 
% 56.93/57.16             X0))),
% 56.93/57.16      inference('sup-', [status(thm)], ['57', '58'])).
% 56.93/57.16  thf('60', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['35', '36'])).
% 56.93/57.16  thf('61', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X2)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X2) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16              = (X2))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (sk_C @ (k1_tarski @ X2) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 56.93/57.16             (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['59', '60'])).
% 56.93/57.16  thf('62', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((sk_C @ (k1_tarski @ X1) @ X0) = (X1))
% 56.93/57.16          | ((k1_tarski @ X1) = (k1_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_C @ (k1_tarski @ X1) @ X0) @ 
% 56.93/57.16              (sk_D_1 @ (sk_C @ (k1_tarski @ X1) @ X0) @ X0)) @ 
% 56.93/57.16             X0))),
% 56.93/57.16      inference('sup-', [status(thm)], ['57', '58'])).
% 56.93/57.16  thf('63', plain,
% 56.93/57.16      (![X20 : $i, X23 : $i, X24 : $i]:
% 56.93/57.16         (((X23) = (k1_relat_1 @ X20))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X23 @ X20) @ X24) @ X20)
% 56.93/57.16          | ~ (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 56.93/57.16      inference('cnf', [status(esa)], [d4_relat_1])).
% 56.93/57.16  thf('64', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((k1_tarski @ X1) = (k1_relat_1 @ X0))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X1) @ X0) = (X1))
% 56.93/57.16          | ~ (r2_hidden @ (sk_C @ (k1_tarski @ X1) @ X0) @ (k1_tarski @ X1))
% 56.93/57.16          | ((k1_tarski @ X1) = (k1_relat_1 @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['62', '63'])).
% 56.93/57.16  thf('65', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (sk_C @ (k1_tarski @ X1) @ X0) @ (k1_tarski @ X1))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X1) @ X0) = (X1))
% 56.93/57.16          | ((k1_tarski @ X1) = (k1_relat_1 @ X0)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['64'])).
% 56.93/57.16  thf('66', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 56.93/57.16            = (X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 56.93/57.16              = (X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['61', '65'])).
% 56.93/57.16  thf('67', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 56.93/57.16              = (X0)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['66'])).
% 56.93/57.16  thf('68', plain,
% 56.93/57.16      (![X20 : $i, X23 : $i]:
% 56.93/57.16         (((X23) = (k1_relat_1 @ X20))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_C @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 56.93/57.16          | (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 56.93/57.16      inference('cnf', [status(esa)], [d4_relat_1])).
% 56.93/57.16  thf('69', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('70', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 56.93/57.16          | ((X1) = (k1_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ X2 @ 
% 56.93/57.16              (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0))) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['68', '69'])).
% 56.93/57.16  thf('71', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         ((r2_hidden @ X11 @ X12)
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('72', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((X2) = (k1_relat_1 @ (k1_tarski @ X0)))
% 56.93/57.16          | (r2_hidden @ (sk_C @ X2 @ (k1_tarski @ X0)) @ X2)
% 56.93/57.16          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['70', '71'])).
% 56.93/57.16  thf('73', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X2))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 56.93/57.16      inference('sup+', [status(thm)], ['67', '72'])).
% 56.93/57.16  thf('74', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ X2 @ (k1_tarski @ X2))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['73'])).
% 56.93/57.16  thf('75', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 56.93/57.16      inference('condensation', [status(thm)], ['74'])).
% 56.93/57.16  thf('76', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('77', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X2))))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['75', '76'])).
% 56.93/57.16  thf('78', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('79', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X2))))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 56.93/57.16      inference('demod', [status(thm)], ['77', '78'])).
% 56.93/57.16  thf('80', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['35', '36'])).
% 56.93/57.16  thf('81', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X2))))
% 56.93/57.16          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['79', '80'])).
% 56.93/57.16  thf('82', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 56.93/57.16              = (X0)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['66'])).
% 56.93/57.16  thf('83', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ((sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 56.93/57.16              = (X0)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['66'])).
% 56.93/57.16  thf('84', plain,
% 56.93/57.16      (![X20 : $i, X23 : $i, X24 : $i]:
% 56.93/57.16         (((X23) = (k1_relat_1 @ X20))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X23 @ X20) @ X24) @ X20)
% 56.93/57.16          | ~ (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 56.93/57.16      inference('cnf', [status(esa)], [d4_relat_1])).
% 56.93/57.16  thf('85', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ~ (r2_hidden @ 
% 56.93/57.16               (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 56.93/57.16               (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['83', '84'])).
% 56.93/57.16  thf('86', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ 
% 56.93/57.16             (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 56.93/57.16             (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 56.93/57.16               (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['85'])).
% 56.93/57.16  thf('87', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 56.93/57.16               (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['82', '86'])).
% 56.93/57.16  thf('88', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['87'])).
% 56.93/57.16  thf('89', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['35', '36'])).
% 56.93/57.16  thf('90', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 56.93/57.16               (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 56.93/57.16      inference('clc', [status(thm)], ['88', '89'])).
% 56.93/57.16  thf('91', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (((k1_tarski @ X2)
% 56.93/57.16            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X3))))
% 56.93/57.16          | ((k1_tarski @ X1)
% 56.93/57.16              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['81', '90'])).
% 56.93/57.16  thf('92', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((k1_tarski @ X0) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 56.93/57.16      inference('condensation', [status(thm)], ['91'])).
% 56.93/57.16  thf('93', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 56.93/57.16         (((k1_tarski @ X1) = (k1_tarski @ X0))
% 56.93/57.16          | (r2_hidden @ X3 @ 
% 56.93/57.16             (k1_relat_1 @ 
% 56.93/57.16              (k2_zfmisc_1 @ (k1_tarski @ X3) @ 
% 56.93/57.16               (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X2))))))
% 56.93/57.16          | (r2_hidden @ X4 @ (k1_tarski @ X4)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['54', '92'])).
% 56.93/57.16  thf('94', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((k1_tarski @ X0) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 56.93/57.16      inference('condensation', [status(thm)], ['91'])).
% 56.93/57.16  thf('95', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('96', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((k1_tarski @ X0) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 56.93/57.16      inference('condensation', [status(thm)], ['91'])).
% 56.93/57.16  thf('97', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X3 : $i, X4 : $i]:
% 56.93/57.16         (((k1_tarski @ X1) = (k1_tarski @ X0))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X3))
% 56.93/57.16          | (r2_hidden @ X4 @ (k1_tarski @ X4)))),
% 56.93/57.16      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 56.93/57.16  thf('98', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0) = (k1_tarski @ X1))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X2)))),
% 56.93/57.16      inference('condensation', [status(thm)], ['97'])).
% 56.93/57.16  thf(d5_relat_1, axiom,
% 56.93/57.16    (![A:$i,B:$i]:
% 56.93/57.16     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 56.93/57.16       ( ![C:$i]:
% 56.93/57.16         ( ( r2_hidden @ C @ B ) <=>
% 56.93/57.16           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 56.93/57.16  thf('99', plain,
% 56.93/57.16      (![X27 : $i, X30 : $i]:
% 56.93/57.16         (((X30) = (k2_relat_1 @ X27))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_1 @ X30 @ X27)) @ X27)
% 56.93/57.16          | (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 56.93/57.16      inference('cnf', [status(esa)], [d5_relat_1])).
% 56.93/57.16  thf('100', plain,
% 56.93/57.16      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 56.93/57.16         (((X7) = (X6))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 56.93/57.16               (k2_zfmisc_1 @ (k1_tarski @ X6) @ X9)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 56.93/57.16  thf('101', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C_1 @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) @ 
% 56.93/57.16           X2)
% 56.93/57.16          | ((X2) = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))
% 56.93/57.16          | ((sk_D_2 @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) = (X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['99', '100'])).
% 56.93/57.16  thf('102', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('103', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (((sk_D_2 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X2) @ X1)) = (X2))
% 56.93/57.16          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X2) @ X1)))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ X3 @ 
% 56.93/57.16              (sk_C_1 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X2) @ X1))) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X3) @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['101', '102'])).
% 56.93/57.16  thf('104', plain,
% 56.93/57.16      (![X27 : $i, X30 : $i, X31 : $i]:
% 56.93/57.16         (((X30) = (k2_relat_1 @ X27))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_1 @ X30 @ X27)) @ X27)
% 56.93/57.16          | ~ (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 56.93/57.16      inference('cnf', [status(esa)], [d5_relat_1])).
% 56.93/57.16  thf('105', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))
% 56.93/57.16          | ((sk_D_2 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) = (X1))
% 56.93/57.16          | ~ (r2_hidden @ 
% 56.93/57.16               (sk_C_1 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) @ X0)
% 56.93/57.16          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['103', '104'])).
% 56.93/57.16  thf('106', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (~ (r2_hidden @ 
% 56.93/57.16             (sk_C_1 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) @ X0)
% 56.93/57.16          | ((sk_D_2 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) = (X1))
% 56.93/57.16          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['105'])).
% 56.93/57.16  thf('107', plain,
% 56.93/57.16      (![X27 : $i, X30 : $i]:
% 56.93/57.16         (((X30) = (k2_relat_1 @ X27))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_1 @ X30 @ X27)) @ X27)
% 56.93/57.16          | (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 56.93/57.16      inference('cnf', [status(esa)], [d5_relat_1])).
% 56.93/57.16  thf('108', plain,
% 56.93/57.16      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 56.93/57.16         ((r2_hidden @ X8 @ X9)
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 56.93/57.16               (k2_zfmisc_1 @ (k1_tarski @ X6) @ X9)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 56.93/57.16  thf('109', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C_1 @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) @ 
% 56.93/57.16           X2)
% 56.93/57.16          | ((X2) = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (sk_C_1 @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) @ X0))),
% 56.93/57.16      inference('sup-', [status(thm)], ['107', '108'])).
% 56.93/57.16  thf('110', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) @ 
% 56.93/57.16           X0)
% 56.93/57.16          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0))))),
% 56.93/57.16      inference('eq_fact', [status(thm)], ['109'])).
% 56.93/57.16  thf('111', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))
% 56.93/57.16          | ((sk_D_2 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)) = (X1)))),
% 56.93/57.16      inference('clc', [status(thm)], ['106', '110'])).
% 56.93/57.16  thf('112', plain,
% 56.93/57.16      (![X27 : $i, X30 : $i]:
% 56.93/57.16         (((X30) = (k2_relat_1 @ X27))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_1 @ X30 @ X27)) @ X27)
% 56.93/57.16          | (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 56.93/57.16      inference('cnf', [status(esa)], [d5_relat_1])).
% 56.93/57.16  thf('113', plain,
% 56.93/57.16      (![X18 : $i, X19 : $i, X20 : $i]:
% 56.93/57.16         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 56.93/57.16      inference('simplify', [status(thm)], ['17'])).
% 56.93/57.16  thf('114', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 56.93/57.16          | ((X1) = (k2_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ (sk_D_2 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['112', '113'])).
% 56.93/57.16  thf('115', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('116', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_D_2 @ X0 @ X1) @ (k1_relat_1 @ X1))
% 56.93/57.16          | ((X0) = (k2_relat_1 @ X1))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ X1)) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X2) @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['114', '115'])).
% 56.93/57.16  thf('117', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         ((r2_hidden @ X11 @ X12)
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('118', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0) = (k2_relat_1 @ X2))
% 56.93/57.16          | (r2_hidden @ (sk_D_2 @ (k1_tarski @ X0) @ X2) @ (k1_relat_1 @ X2))
% 56.93/57.16          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['116', '117'])).
% 56.93/57.16  thf('119', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ X0 @ 
% 56.93/57.16           (k1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))
% 56.93/57.16          | ((k1_tarski @ X1)
% 56.93/57.16              = (k2_relat_1 @ 
% 56.93/57.16                 (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X2))
% 56.93/57.16          | ((k1_tarski @ X1)
% 56.93/57.16              = (k2_relat_1 @ 
% 56.93/57.16                 (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))))),
% 56.93/57.16      inference('sup+', [status(thm)], ['111', '118'])).
% 56.93/57.16  thf('120', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('121', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((k1_tarski @ X0) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 56.93/57.16      inference('condensation', [status(thm)], ['91'])).
% 56.93/57.16  thf('122', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('123', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('124', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X1)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X2))
% 56.93/57.16          | ((k1_tarski @ X1)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 56.93/57.16      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 56.93/57.16  thf('125', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ X2 @ (k1_tarski @ X2))
% 56.93/57.16          | ((k1_tarski @ X1)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 56.93/57.16          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['124'])).
% 56.93/57.16  thf('126', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X1)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 56.93/57.16      inference('condensation', [status(thm)], ['125'])).
% 56.93/57.16  thf('127', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (((k1_tarski @ X1) = (k2_relat_1 @ (k1_tarski @ X0)))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X3))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X2)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['98', '126'])).
% 56.93/57.16  thf('128', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0) = (k2_relat_1 @ (k1_tarski @ X1)))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X2)))),
% 56.93/57.16      inference('condensation', [status(thm)], ['127'])).
% 56.93/57.16  thf('129', plain,
% 56.93/57.16      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A))
% 56.93/57.16        | ((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf('130', plain,
% 56.93/57.16      ((((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B)))
% 56.93/57.16         <= (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B))))),
% 56.93/57.16      inference('split', [status(esa)], ['129'])).
% 56.93/57.16  thf('131', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf('132', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['14'])).
% 56.93/57.16  thf('133', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf('134', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((sk_C @ X0 @ sk_C_2) = (sk_A))
% 56.93/57.16          | ((X0) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C @ X0 @ sk_C_2)) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['8', '10'])).
% 56.93/57.16  thf('135', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf('136', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         ((r2_hidden @ X11 @ X12)
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('137', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k2_zfmisc_1 @ X0 @ sk_C_2))
% 56.93/57.16          | (r2_hidden @ X2 @ X0))),
% 56.93/57.16      inference('sup-', [status(thm)], ['135', '136'])).
% 56.93/57.16  thf('138', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ((sk_C @ sk_C_2 @ sk_C_2) = (sk_A))
% 56.93/57.16          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['134', '137'])).
% 56.93/57.16  thf('139', plain,
% 56.93/57.16      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)
% 56.93/57.16        | ((sk_C @ sk_C_2 @ sk_C_2) = (sk_A))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['133', '138'])).
% 56.93/57.16  thf('140', plain,
% 56.93/57.16      (![X18 : $i, X19 : $i, X20 : $i]:
% 56.93/57.16         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 56.93/57.16      inference('simplify', [status(thm)], ['17'])).
% 56.93/57.16  thf('141', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C @ sk_C_2 @ sk_C_2) = (sk_A))
% 56.93/57.16        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['139', '140'])).
% 56.93/57.16  thf('142', plain,
% 56.93/57.16      (![X20 : $i, X22 : $i]:
% 56.93/57.16         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 56.93/57.16          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['41'])).
% 56.93/57.16  thf('143', plain,
% 56.93/57.16      ((((sk_C @ sk_C_2 @ sk_C_2) = (sk_A))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_C_2)) @ sk_C_2))),
% 56.93/57.16      inference('sup-', [status(thm)], ['141', '142'])).
% 56.93/57.16  thf('144', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2))),
% 56.93/57.16      inference('clc', [status(thm)], ['33', '38'])).
% 56.93/57.16  thf('145', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C @ sk_C_2 @ sk_C_2) = (sk_A))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['143', '144'])).
% 56.93/57.16  thf('146', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C @ sk_C_2 @ sk_C_2) = (sk_A))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['143', '144'])).
% 56.93/57.16  thf('147', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 56.93/57.16          | ((X1) = (k1_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['16', '18'])).
% 56.93/57.16  thf('148', plain,
% 56.93/57.16      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ (sk_C @ sk_C_2 @ sk_C_2) @ sk_C_2))),
% 56.93/57.16      inference('sup+', [status(thm)], ['146', '147'])).
% 56.93/57.16  thf('149', plain,
% 56.93/57.16      (((r2_hidden @ (sk_C @ sk_C_2 @ sk_C_2) @ sk_C_2)
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['148'])).
% 56.93/57.16  thf('150', plain,
% 56.93/57.16      (((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['145', '149'])).
% 56.93/57.16  thf('151', plain,
% 56.93/57.16      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ sk_A @ sk_C_2))),
% 56.93/57.16      inference('simplify', [status(thm)], ['150'])).
% 56.93/57.16  thf('152', plain,
% 56.93/57.16      (![X20 : $i, X22 : $i]:
% 56.93/57.16         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 56.93/57.16          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['41'])).
% 56.93/57.16  thf('153', plain,
% 56.93/57.16      (((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_C_2)) @ sk_C_2))),
% 56.93/57.16      inference('sup-', [status(thm)], ['151', '152'])).
% 56.93/57.16  thf('154', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2))),
% 56.93/57.16      inference('clc', [status(thm)], ['33', '38'])).
% 56.93/57.16  thf('155', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['153', '154'])).
% 56.93/57.16  thf('156', plain,
% 56.93/57.16      (((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['155'])).
% 56.93/57.16  thf('157', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('158', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C_2)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['156', '157'])).
% 56.93/57.16  thf('159', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf('160', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         (((X13) = (X14))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('161', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k2_zfmisc_1 @ X0 @ sk_C_2))
% 56.93/57.16          | ((X1) = (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['159', '160'])).
% 56.93/57.16  thf('162', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_A) = (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['158', '161'])).
% 56.93/57.16  thf('163', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2))),
% 56.93/57.16      inference('clc', [status(thm)], ['33', '38'])).
% 56.93/57.16  thf('164', plain,
% 56.93/57.16      ((~ (r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['162', '163'])).
% 56.93/57.16  thf('165', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ~ (r2_hidden @ sk_A @ sk_C_2))),
% 56.93/57.16      inference('simplify', [status(thm)], ['164'])).
% 56.93/57.16  thf('166', plain,
% 56.93/57.16      (((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C_2) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['155'])).
% 56.93/57.16  thf('167', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('clc', [status(thm)], ['165', '166'])).
% 56.93/57.16  thf('168', plain,
% 56.93/57.16      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('split', [status(esa)], ['129'])).
% 56.93/57.16  thf('169', plain,
% 56.93/57.16      (((((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_C_2))
% 56.93/57.16         | ((sk_C_2) = (k1_relat_1 @ sk_C_2))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['167', '168'])).
% 56.93/57.16  thf('170', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['169'])).
% 56.93/57.16  thf('171', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['14'])).
% 56.93/57.16  thf('172', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 56.93/57.16          | ((X1) = (k1_relat_1 @ X0))
% 56.93/57.16          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['16', '18'])).
% 56.93/57.16  thf('173', plain,
% 56.93/57.16      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 56.93/57.16           (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['171', '172'])).
% 56.93/57.16  thf('174', plain,
% 56.93/57.16      (((r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 56.93/57.16         (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16        | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['173'])).
% 56.93/57.16  thf('175', plain,
% 56.93/57.16      ((((r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ sk_C_2)
% 56.93/57.16         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 56.93/57.16         | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup+', [status(thm)], ['170', '174'])).
% 56.93/57.16  thf('176', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['169'])).
% 56.93/57.16  thf('177', plain,
% 56.93/57.16      ((((r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ sk_C_2)
% 56.93/57.16         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 56.93/57.16         | ((k1_tarski @ sk_A) = (sk_C_2))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('demod', [status(thm)], ['175', '176'])).
% 56.93/57.16  thf('178', plain,
% 56.93/57.16      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('split', [status(esa)], ['129'])).
% 56.93/57.16  thf('179', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['169'])).
% 56.93/57.16  thf('180', plain,
% 56.93/57.16      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('demod', [status(thm)], ['178', '179'])).
% 56.93/57.16  thf('181', plain,
% 56.93/57.16      ((((r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ sk_C_2)
% 56.93/57.16         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify_reflect-', [status(thm)], ['177', '180'])).
% 56.93/57.16  thf('182', plain,
% 56.93/57.16      ((((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16         | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup+', [status(thm)], ['132', '181'])).
% 56.93/57.16  thf('183', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['169'])).
% 56.93/57.16  thf('184', plain,
% 56.93/57.16      ((((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16         | ((k1_tarski @ sk_A) = (sk_C_2))
% 56.93/57.16         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('demod', [status(thm)], ['182', '183'])).
% 56.93/57.16  thf('185', plain,
% 56.93/57.16      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('demod', [status(thm)], ['178', '179'])).
% 56.93/57.16  thf('186', plain,
% 56.93/57.16      ((((r2_hidden @ sk_A @ sk_C_2) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify_reflect-', [status(thm)], ['184', '185'])).
% 56.93/57.16  thf('187', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('188', plain,
% 56.93/57.16      ((![X0 : $i]:
% 56.93/57.16          ((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16           | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ 
% 56.93/57.16              (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['186', '187'])).
% 56.93/57.16  thf('189', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('190', plain,
% 56.93/57.16      ((![X0 : $i]:
% 56.93/57.16          ((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16           | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ 
% 56.93/57.16              (k1_tarski @ (k4_tarski @ X0 @ sk_A)))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('demod', [status(thm)], ['188', '189'])).
% 56.93/57.16  thf('191', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['35', '36'])).
% 56.93/57.16  thf('192', plain,
% 56.93/57.16      ((![X0 : $i]:
% 56.93/57.16          ((r2_hidden @ sk_A @ sk_C_2) | (r2_hidden @ X0 @ (k1_tarski @ X0))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['190', '191'])).
% 56.93/57.16  thf('193', plain,
% 56.93/57.16      ((((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)
% 56.93/57.16         | (r2_hidden @ sk_A @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup+', [status(thm)], ['131', '192'])).
% 56.93/57.16  thf('194', plain,
% 56.93/57.16      (![X18 : $i, X19 : $i, X20 : $i]:
% 56.93/57.16         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 56.93/57.16      inference('simplify', [status(thm)], ['17'])).
% 56.93/57.16  thf('195', plain,
% 56.93/57.16      ((((r2_hidden @ sk_A @ sk_C_2)
% 56.93/57.16         | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['193', '194'])).
% 56.93/57.16  thf('196', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['169'])).
% 56.93/57.16  thf('197', plain,
% 56.93/57.16      ((((r2_hidden @ sk_A @ sk_C_2) | (r2_hidden @ sk_A @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('demod', [status(thm)], ['195', '196'])).
% 56.93/57.16  thf('198', plain,
% 56.93/57.16      (((r2_hidden @ sk_A @ sk_C_2))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['197'])).
% 56.93/57.16  thf('199', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['169'])).
% 56.93/57.16  thf('200', plain,
% 56.93/57.16      (![X20 : $i, X22 : $i]:
% 56.93/57.16         ((r2_hidden @ (k4_tarski @ X22 @ (sk_D_1 @ X22 @ X20)) @ X20)
% 56.93/57.16          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X20)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['41'])).
% 56.93/57.16  thf('201', plain,
% 56.93/57.16      ((![X0 : $i]:
% 56.93/57.16          (~ (r2_hidden @ X0 @ sk_C_2)
% 56.93/57.16           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_2)) @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['199', '200'])).
% 56.93/57.16  thf('202', plain,
% 56.93/57.16      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_C_2)) @ sk_C_2))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['198', '201'])).
% 56.93/57.16  thf('203', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2))),
% 56.93/57.16      inference('clc', [status(thm)], ['33', '38'])).
% 56.93/57.16  thf('204', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['202', '203'])).
% 56.93/57.16  thf('205', plain,
% 56.93/57.16      ((((sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['169'])).
% 56.93/57.16  thf('206', plain,
% 56.93/57.16      ((((k1_tarski @ sk_A) = (sk_C_2)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('demod', [status(thm)], ['204', '205'])).
% 56.93/57.16  thf('207', plain,
% 56.93/57.16      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 56.93/57.16         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 56.93/57.16      inference('demod', [status(thm)], ['178', '179'])).
% 56.93/57.16  thf('208', plain, ((((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A)))),
% 56.93/57.16      inference('simplify_reflect-', [status(thm)], ['206', '207'])).
% 56.93/57.16  thf('209', plain,
% 56.93/57.16      (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B))) | 
% 56.93/57.16       ~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A)))),
% 56.93/57.16      inference('split', [status(esa)], ['129'])).
% 56.93/57.16  thf('210', plain, (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B)))),
% 56.93/57.16      inference('sat_resolution*', [status(thm)], ['208', '209'])).
% 56.93/57.16  thf('211', plain, (((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B))),
% 56.93/57.16      inference('simpl_trail', [status(thm)], ['130', '210'])).
% 56.93/57.16  thf('212', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((k2_relat_1 @ sk_C_2) != (k2_relat_1 @ (k1_tarski @ X0)))
% 56.93/57.16          | (r2_hidden @ X1 @ (k1_tarski @ X1)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['128', '211'])).
% 56.93/57.16  thf('213', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 56.93/57.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.93/57.16  thf('214', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('215', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ X0))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ X0)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['213', '214'])).
% 56.93/57.16  thf('216', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X0) = (k1_tarski @ X1))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X2)))),
% 56.93/57.16      inference('condensation', [status(thm)], ['97'])).
% 56.93/57.16  thf('217', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((k1_tarski @ X0) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 56.93/57.16      inference('condensation', [status(thm)], ['91'])).
% 56.93/57.16  thf('218', plain,
% 56.93/57.16      (![X0 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (((k1_tarski @ X2) = (k1_relat_1 @ (k1_tarski @ X0)))
% 56.93/57.16          | (r2_hidden @ X3 @ (k1_tarski @ X3)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['216', '217'])).
% 56.93/57.16  thf('219', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X1)
% 56.93/57.16            = (k1_relat_1 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ X0))))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X2)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['215', '218'])).
% 56.93/57.16  thf('220', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ X0))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ X0)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['213', '214'])).
% 56.93/57.16  thf('221', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((k1_tarski @ X0) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 56.93/57.16      inference('condensation', [status(thm)], ['91'])).
% 56.93/57.16  thf('222', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((k1_tarski @ (k4_tarski @ sk_A @ sk_B))
% 56.93/57.16           = (k1_relat_1 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ X0))))),
% 56.93/57.16      inference('sup+', [status(thm)], ['220', '221'])).
% 56.93/57.16  thf('223', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ X0))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 56.93/57.16      inference('sup+', [status(thm)], ['45', '46'])).
% 56.93/57.16  thf('224', plain,
% 56.93/57.16      (((sk_C_2) = (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ sk_B)))),
% 56.93/57.16      inference('demod', [status(thm)], ['0', '47'])).
% 56.93/57.16  thf('225', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((sk_C_2) = (k1_relat_1 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ X0))))),
% 56.93/57.16      inference('demod', [status(thm)], ['222', '223', '224'])).
% 56.93/57.16  thf('226', plain,
% 56.93/57.16      (![X1 : $i, X2 : $i]:
% 56.93/57.16         (((k1_tarski @ X1) = (sk_C_2)) | (r2_hidden @ X2 @ (k1_tarski @ X2)))),
% 56.93/57.16      inference('demod', [status(thm)], ['219', '225'])).
% 56.93/57.16  thf('227', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 56.93/57.16      inference('clc', [status(thm)], ['212', '226'])).
% 56.93/57.16  thf('228', plain,
% 56.93/57.16      (![X27 : $i, X30 : $i]:
% 56.93/57.16         (((X30) = (k2_relat_1 @ X27))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_1 @ X30 @ X27)) @ X27)
% 56.93/57.16          | (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 56.93/57.16      inference('cnf', [status(esa)], [d5_relat_1])).
% 56.93/57.16  thf('229', plain,
% 56.93/57.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 56.93/57.16         (((X13) = (X14))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 56.93/57.16               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 56.93/57.16      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 56.93/57.16  thf('230', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C_1 @ X2 @ (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))) @ 
% 56.93/57.16           X2)
% 56.93/57.16          | ((X2) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))
% 56.93/57.16          | ((sk_C_1 @ X2 @ (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))) = (X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['228', '229'])).
% 56.93/57.16  thf('231', plain,
% 56.93/57.16      (![X6 : $i, X8 : $i, X10 : $i]:
% 56.93/57.16         (~ (r2_hidden @ X8 @ X10)
% 56.93/57.16          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 56.93/57.16      inference('simplify', [status(thm)], ['9'])).
% 56.93/57.16  thf('232', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (((sk_C_1 @ X0 @ (k2_zfmisc_1 @ X2 @ (k1_tarski @ X1))) = (X1))
% 56.93/57.16          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X2 @ (k1_tarski @ X1))))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ X3 @ 
% 56.93/57.16              (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X2 @ (k1_tarski @ X1)))) @ 
% 56.93/57.16             (k2_zfmisc_1 @ (k1_tarski @ X3) @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['230', '231'])).
% 56.93/57.16  thf('233', plain,
% 56.93/57.16      (![X27 : $i, X30 : $i, X31 : $i]:
% 56.93/57.16         (((X30) = (k2_relat_1 @ X27))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_1 @ X30 @ X27)) @ X27)
% 56.93/57.16          | ~ (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 56.93/57.16      inference('cnf', [status(esa)], [d5_relat_1])).
% 56.93/57.16  thf('234', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k2_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))
% 56.93/57.16          | ((sk_C_1 @ (k1_tarski @ X0) @ 
% 56.93/57.16              (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))) = (X0))
% 56.93/57.16          | ~ (r2_hidden @ 
% 56.93/57.16               (sk_C_1 @ (k1_tarski @ X0) @ 
% 56.93/57.16                (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))) @ 
% 56.93/57.16               (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ 
% 56.93/57.16                 (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['232', '233'])).
% 56.93/57.16  thf('235', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('236', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('237', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('238', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('239', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 56.93/57.16          | ((sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16              = (X0))
% 56.93/57.16          | ~ (r2_hidden @ 
% 56.93/57.16               (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 56.93/57.16               (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 56.93/57.16      inference('demod', [status(thm)], ['234', '235', '236', '237', '238'])).
% 56.93/57.16  thf('240', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (~ (r2_hidden @ 
% 56.93/57.16             (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 56.93/57.16             (k1_tarski @ X0))
% 56.93/57.16          | ((sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16              = (X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['239'])).
% 56.93/57.16  thf('241', plain,
% 56.93/57.16      (![X27 : $i, X30 : $i]:
% 56.93/57.16         (((X30) = (k2_relat_1 @ X27))
% 56.93/57.16          | (r2_hidden @ 
% 56.93/57.16             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_1 @ X30 @ X27)) @ X27)
% 56.93/57.16          | (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 56.93/57.16      inference('cnf', [status(esa)], [d5_relat_1])).
% 56.93/57.16  thf('242', plain,
% 56.93/57.16      (![X16 : $i, X17 : $i]:
% 56.93/57.16         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 56.93/57.16           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 56.93/57.16  thf('243', plain,
% 56.93/57.16      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 56.93/57.16         ((r2_hidden @ X8 @ X9)
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 56.93/57.16               (k2_zfmisc_1 @ (k1_tarski @ X6) @ X9)))),
% 56.93/57.16      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 56.93/57.16  thf('244', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | (r2_hidden @ X2 @ (k1_tarski @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['242', '243'])).
% 56.93/57.16  thf('245', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         ((r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 56.93/57.16          | ((X2) = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 56.93/57.16          | (r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 56.93/57.16             (k1_tarski @ X0)))),
% 56.93/57.16      inference('sup-', [status(thm)], ['241', '244'])).
% 56.93/57.16  thf('246', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ 
% 56.93/57.16           (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 56.93/57.16           (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 56.93/57.16      inference('eq_fact', [status(thm)], ['245'])).
% 56.93/57.16  thf('247', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         (((k1_tarski @ X0)
% 56.93/57.16            = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 56.93/57.16          | ((sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16              = (X0)))),
% 56.93/57.16      inference('clc', [status(thm)], ['240', '246'])).
% 56.93/57.16  thf('248', plain,
% 56.93/57.16      (![X27 : $i, X30 : $i, X31 : $i]:
% 56.93/57.16         (((X30) = (k2_relat_1 @ X27))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_1 @ X30 @ X27)) @ X27)
% 56.93/57.16          | ~ (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 56.93/57.16      inference('cnf', [status(esa)], [d5_relat_1])).
% 56.93/57.16  thf('249', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 56.93/57.16          | ~ (r2_hidden @ 
% 56.93/57.16               (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 56.93/57.16               (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['247', '248'])).
% 56.93/57.16  thf('250', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ 
% 56.93/57.16             (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 56.93/57.16             (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 56.93/57.16          | ~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 56.93/57.16               (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 56.93/57.16      inference('simplify', [status(thm)], ['249'])).
% 56.93/57.16  thf('251', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((r2_hidden @ 
% 56.93/57.16           (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 56.93/57.16           (k1_tarski @ X0))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 56.93/57.16      inference('eq_fact', [status(thm)], ['245'])).
% 56.93/57.16  thf('252', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.93/57.16         (~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 56.93/57.16             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 56.93/57.16          | ((k1_tarski @ X0)
% 56.93/57.16              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 56.93/57.16      inference('clc', [status(thm)], ['250', '251'])).
% 56.93/57.16  thf('253', plain,
% 56.93/57.16      (![X0 : $i, X1 : $i]:
% 56.93/57.16         ((k1_tarski @ X0) = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 56.93/57.16      inference('sup-', [status(thm)], ['227', '252'])).
% 56.93/57.16  thf('254', plain,
% 56.93/57.16      (![X0 : $i]:
% 56.93/57.16         ((k1_tarski @ X0)
% 56.93/57.16           = (k2_relat_1 @ 
% 56.93/57.16              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ X0))))),
% 56.93/57.16      inference('sup+', [status(thm)], ['49', '253'])).
% 56.93/57.16  thf('255', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))),
% 56.93/57.16      inference('sup+', [status(thm)], ['48', '254'])).
% 56.93/57.16  thf('256', plain, (((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B))),
% 56.93/57.16      inference('simpl_trail', [status(thm)], ['130', '210'])).
% 56.93/57.16  thf('257', plain, ($false),
% 56.93/57.16      inference('simplify_reflect-', [status(thm)], ['255', '256'])).
% 56.93/57.16  
% 56.93/57.16  % SZS output end Refutation
% 56.93/57.16  
% 56.93/57.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
