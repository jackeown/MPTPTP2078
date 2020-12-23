%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.STnrkHOR9g

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:44 EST 2020

% Result     : Theorem 17.42s
% Output     : Refutation 17.42s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 272 expanded)
%              Number of leaves         :   23 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  887 (3333 expanded)
%              Number of equality atoms :   78 ( 323 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X15 ) ) )
      | ( X13 != X15 )
      | ( X12 != X11 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('3',plain,(
    ! [X11: $i,X15: $i] :
      ( r2_hidden @ ( k4_tarski @ X11 @ X15 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('5',plain,(
    ! [X11: $i,X15: $i] :
      ( r2_hidden @ ( k4_tarski @ X11 @ X15 ) @ ( k1_tarski @ ( k4_tarski @ X11 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,
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

thf('8',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,
    ( sk_C_2
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ( X2 != X1 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('18',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8 = X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X23 @ X20 ) @ X24 ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_2 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_C_2
    = ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('38',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X30 @ X27 ) @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      = ( k1_tarski @ ( k4_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ ( k1_tarski @ ( k4_tarski @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X30
        = ( k2_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_C_1 @ X30 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X30 @ X27 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['42'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['37','52'])).

thf('54',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['36','53'])).

thf('55',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['55'])).

thf('59',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['55'])).

thf('62',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['56','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.STnrkHOR9g
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 17.42/17.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.42/17.64  % Solved by: fo/fo7.sh
% 17.42/17.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.42/17.64  % done 7455 iterations in 17.169s
% 17.42/17.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.42/17.64  % SZS output start Refutation
% 17.42/17.64  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 17.42/17.64  thf(sk_A_type, type, sk_A: $i).
% 17.42/17.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.42/17.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 17.42/17.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 17.42/17.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 17.42/17.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.42/17.64  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 17.42/17.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.42/17.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.42/17.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 17.42/17.64  thf(sk_B_type, type, sk_B: $i).
% 17.42/17.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 17.42/17.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.42/17.64  thf(sk_C_2_type, type, sk_C_2: $i).
% 17.42/17.64  thf(t23_relat_1, conjecture,
% 17.42/17.64    (![A:$i,B:$i,C:$i]:
% 17.42/17.64     ( ( v1_relat_1 @ C ) =>
% 17.42/17.64       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 17.42/17.64         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 17.42/17.64           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 17.42/17.64  thf(zf_stmt_0, negated_conjecture,
% 17.42/17.64    (~( ![A:$i,B:$i,C:$i]:
% 17.42/17.64        ( ( v1_relat_1 @ C ) =>
% 17.42/17.64          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 17.42/17.64            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 17.42/17.64              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 17.42/17.64    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 17.42/17.64  thf('0', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 17.42/17.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.42/17.64  thf('1', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 17.42/17.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.42/17.64  thf(t34_zfmisc_1, axiom,
% 17.42/17.64    (![A:$i,B:$i,C:$i,D:$i]:
% 17.42/17.64     ( ( r2_hidden @
% 17.42/17.64         ( k4_tarski @ A @ B ) @ 
% 17.42/17.64         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 17.42/17.64       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 17.42/17.64  thf('2', plain,
% 17.42/17.64      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 17.42/17.64         ((r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 17.42/17.64           (k2_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X15)))
% 17.42/17.64          | ((X13) != (X15))
% 17.42/17.64          | ((X12) != (X11)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 17.42/17.64  thf('3', plain,
% 17.42/17.64      (![X11 : $i, X15 : $i]:
% 17.42/17.64         (r2_hidden @ (k4_tarski @ X11 @ X15) @ 
% 17.42/17.64          (k2_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X15)))),
% 17.42/17.64      inference('simplify', [status(thm)], ['2'])).
% 17.42/17.64  thf(t35_zfmisc_1, axiom,
% 17.42/17.64    (![A:$i,B:$i]:
% 17.42/17.64     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 17.42/17.64       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 17.42/17.64  thf('4', plain,
% 17.42/17.64      (![X16 : $i, X17 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 17.42/17.64  thf('5', plain,
% 17.42/17.64      (![X11 : $i, X15 : $i]:
% 17.42/17.64         (r2_hidden @ (k4_tarski @ X11 @ X15) @ 
% 17.42/17.64          (k1_tarski @ (k4_tarski @ X11 @ X15)))),
% 17.42/17.64      inference('demod', [status(thm)], ['3', '4'])).
% 17.42/17.64  thf('6', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_2)),
% 17.42/17.64      inference('sup+', [status(thm)], ['1', '5'])).
% 17.42/17.64  thf('7', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 17.42/17.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.42/17.64  thf(d4_relat_1, axiom,
% 17.42/17.64    (![A:$i,B:$i]:
% 17.42/17.64     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 17.42/17.64       ( ![C:$i]:
% 17.42/17.64         ( ( r2_hidden @ C @ B ) <=>
% 17.42/17.64           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 17.42/17.64  thf('8', plain,
% 17.42/17.64      (![X20 : $i, X23 : $i]:
% 17.42/17.64         (((X23) = (k1_relat_1 @ X20))
% 17.42/17.64          | (r2_hidden @ 
% 17.42/17.64             (k4_tarski @ (sk_C @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 17.42/17.64          | (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 17.42/17.64      inference('cnf', [status(esa)], [d4_relat_1])).
% 17.42/17.64  thf('9', plain,
% 17.42/17.64      (![X16 : $i, X17 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 17.42/17.64  thf(t129_zfmisc_1, axiom,
% 17.42/17.64    (![A:$i,B:$i,C:$i,D:$i]:
% 17.42/17.64     ( ( r2_hidden @
% 17.42/17.64         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 17.42/17.64       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 17.42/17.64  thf('10', plain,
% 17.42/17.64      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 17.42/17.64         ((r2_hidden @ X6 @ X7)
% 17.42/17.64          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 17.42/17.64               (k2_zfmisc_1 @ X7 @ (k1_tarski @ X9))))),
% 17.42/17.64      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 17.42/17.64  thf('11', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.42/17.64         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 17.42/17.64             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 17.42/17.64          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 17.42/17.64      inference('sup-', [status(thm)], ['9', '10'])).
% 17.42/17.64  thf('12', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.42/17.64         ((r2_hidden @ (sk_C @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 17.42/17.64          | ((X2) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 17.42/17.64          | (r2_hidden @ (sk_C @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 17.42/17.64             (k1_tarski @ X1)))),
% 17.42/17.64      inference('sup-', [status(thm)], ['8', '11'])).
% 17.42/17.64  thf('13', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i]:
% 17.42/17.64         ((r2_hidden @ 
% 17.42/17.64           (sk_C @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 17.42/17.64           (k1_tarski @ X0))
% 17.42/17.64          | ((k1_tarski @ X0)
% 17.42/17.64              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 17.42/17.64      inference('eq_fact', [status(thm)], ['12'])).
% 17.42/17.64  thf('14', plain,
% 17.42/17.64      (((r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ (k1_tarski @ sk_A))
% 17.42/17.64        | ((k1_tarski @ sk_A)
% 17.42/17.64            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))))),
% 17.42/17.64      inference('sup+', [status(thm)], ['7', '13'])).
% 17.42/17.64  thf('15', plain, (((sk_C_2) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 17.42/17.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.42/17.64  thf('16', plain,
% 17.42/17.64      (((r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ (k1_tarski @ sk_A))
% 17.42/17.64        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 17.42/17.64      inference('demod', [status(thm)], ['14', '15'])).
% 17.42/17.64  thf(t128_zfmisc_1, axiom,
% 17.42/17.64    (![A:$i,B:$i,C:$i,D:$i]:
% 17.42/17.64     ( ( r2_hidden @
% 17.42/17.64         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 17.42/17.64       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 17.42/17.64  thf('17', plain,
% 17.42/17.64      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 17.42/17.64         ((r2_hidden @ (k4_tarski @ X2 @ X3) @ 
% 17.42/17.64           (k2_zfmisc_1 @ (k1_tarski @ X1) @ X5))
% 17.42/17.64          | ~ (r2_hidden @ X3 @ X5)
% 17.42/17.64          | ((X2) != (X1)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 17.42/17.64  thf('18', plain,
% 17.42/17.64      (![X1 : $i, X3 : $i, X5 : $i]:
% 17.42/17.64         (~ (r2_hidden @ X3 @ X5)
% 17.42/17.64          | (r2_hidden @ (k4_tarski @ X1 @ X3) @ 
% 17.42/17.64             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X5)))),
% 17.42/17.64      inference('simplify', [status(thm)], ['17'])).
% 17.42/17.64  thf('19', plain,
% 17.42/17.64      (![X0 : $i]:
% 17.42/17.64         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 17.42/17.64          | (r2_hidden @ 
% 17.42/17.64             (k4_tarski @ X0 @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2)) @ 
% 17.42/17.64             (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A))))),
% 17.42/17.64      inference('sup-', [status(thm)], ['16', '18'])).
% 17.42/17.64  thf('20', plain,
% 17.42/17.64      (![X16 : $i, X17 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 17.42/17.64  thf('21', plain,
% 17.42/17.64      (![X0 : $i]:
% 17.42/17.64         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 17.42/17.64          | (r2_hidden @ 
% 17.42/17.64             (k4_tarski @ X0 @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2)) @ 
% 17.42/17.64             (k1_tarski @ (k4_tarski @ X0 @ sk_A))))),
% 17.42/17.64      inference('demod', [status(thm)], ['19', '20'])).
% 17.42/17.64  thf(t69_enumset1, axiom,
% 17.42/17.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 17.42/17.64  thf('22', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 17.42/17.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 17.42/17.64  thf('23', plain,
% 17.42/17.64      (![X16 : $i, X17 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 17.42/17.64  thf('24', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ X0 @ X1)))),
% 17.42/17.64      inference('sup+', [status(thm)], ['22', '23'])).
% 17.42/17.64  thf('25', plain,
% 17.42/17.64      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 17.42/17.64         (((X8) = (X9))
% 17.42/17.64          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 17.42/17.64               (k2_zfmisc_1 @ X7 @ (k1_tarski @ X9))))),
% 17.42/17.64      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 17.42/17.64  thf('26', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.42/17.64         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 17.42/17.64             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 17.42/17.64          | ((X2) = (X0)))),
% 17.42/17.64      inference('sup-', [status(thm)], ['24', '25'])).
% 17.42/17.64  thf('27', plain,
% 17.42/17.64      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 17.42/17.64        | ((sk_C @ (k1_tarski @ sk_A) @ sk_C_2) = (sk_A)))),
% 17.42/17.64      inference('sup-', [status(thm)], ['21', '26'])).
% 17.42/17.64  thf('28', plain,
% 17.42/17.64      (![X20 : $i, X23 : $i, X24 : $i]:
% 17.42/17.64         (((X23) = (k1_relat_1 @ X20))
% 17.42/17.64          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X23 @ X20) @ X24) @ X20)
% 17.42/17.64          | ~ (r2_hidden @ (sk_C @ X23 @ X20) @ X23))),
% 17.42/17.64      inference('cnf', [status(esa)], [d4_relat_1])).
% 17.42/17.64  thf('29', plain,
% 17.42/17.64      (![X0 : $i]:
% 17.42/17.64         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 17.42/17.64          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 17.42/17.64          | ~ (r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 17.42/17.64               (k1_tarski @ sk_A))
% 17.42/17.64          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 17.42/17.64      inference('sup-', [status(thm)], ['27', '28'])).
% 17.42/17.64  thf('30', plain,
% 17.42/17.64      (![X0 : $i]:
% 17.42/17.64         (~ (r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 17.42/17.64             (k1_tarski @ sk_A))
% 17.42/17.64          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))
% 17.42/17.64          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2))),
% 17.42/17.64      inference('simplify', [status(thm)], ['29'])).
% 17.42/17.64  thf('31', plain,
% 17.42/17.64      (((r2_hidden @ (sk_C @ (k1_tarski @ sk_A) @ sk_C_2) @ (k1_tarski @ sk_A))
% 17.42/17.64        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 17.42/17.64      inference('demod', [status(thm)], ['14', '15'])).
% 17.42/17.64  thf('32', plain,
% 17.42/17.64      (![X0 : $i]:
% 17.42/17.64         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_2)
% 17.42/17.64          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 17.42/17.64      inference('clc', [status(thm)], ['30', '31'])).
% 17.42/17.64  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 17.42/17.64      inference('sup-', [status(thm)], ['6', '32'])).
% 17.42/17.64  thf('34', plain,
% 17.42/17.64      (![X16 : $i, X17 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 17.42/17.64  thf('35', plain,
% 17.42/17.64      (![X0 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ X0))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 17.42/17.64      inference('sup+', [status(thm)], ['33', '34'])).
% 17.42/17.64  thf('36', plain,
% 17.42/17.64      (((sk_C_2) = (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ sk_B)))),
% 17.42/17.64      inference('demod', [status(thm)], ['0', '35'])).
% 17.42/17.64  thf('37', plain,
% 17.42/17.64      (![X0 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ X0))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 17.42/17.64      inference('sup+', [status(thm)], ['33', '34'])).
% 17.42/17.64  thf(d5_relat_1, axiom,
% 17.42/17.64    (![A:$i,B:$i]:
% 17.42/17.64     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 17.42/17.64       ( ![C:$i]:
% 17.42/17.64         ( ( r2_hidden @ C @ B ) <=>
% 17.42/17.64           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 17.42/17.64  thf('38', plain,
% 17.42/17.64      (![X27 : $i, X30 : $i]:
% 17.42/17.64         (((X30) = (k2_relat_1 @ X27))
% 17.42/17.64          | (r2_hidden @ 
% 17.42/17.64             (k4_tarski @ (sk_D_2 @ X30 @ X27) @ (sk_C_1 @ X30 @ X27)) @ X27)
% 17.42/17.64          | (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 17.42/17.64      inference('cnf', [status(esa)], [d5_relat_1])).
% 17.42/17.64  thf('39', plain,
% 17.42/17.64      (![X16 : $i, X17 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 17.42/17.64  thf('40', plain,
% 17.42/17.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.42/17.64         ((r2_hidden @ X3 @ X4)
% 17.42/17.64          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ 
% 17.42/17.64               (k2_zfmisc_1 @ (k1_tarski @ X1) @ X4)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 17.42/17.64  thf('41', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.42/17.64         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 17.42/17.64             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 17.42/17.64          | (r2_hidden @ X2 @ (k1_tarski @ X0)))),
% 17.42/17.64      inference('sup-', [status(thm)], ['39', '40'])).
% 17.42/17.64  thf('42', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.42/17.64         ((r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 17.42/17.64          | ((X2) = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 17.42/17.64          | (r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 17.42/17.64             (k1_tarski @ X0)))),
% 17.42/17.64      inference('sup-', [status(thm)], ['38', '41'])).
% 17.42/17.64  thf('43', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i]:
% 17.42/17.64         ((r2_hidden @ 
% 17.42/17.64           (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 17.42/17.64           (k1_tarski @ X0))
% 17.42/17.64          | ((k1_tarski @ X0)
% 17.42/17.64              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 17.42/17.64      inference('eq_fact', [status(thm)], ['42'])).
% 17.42/17.64  thf('44', plain,
% 17.42/17.64      (![X1 : $i, X3 : $i, X5 : $i]:
% 17.42/17.64         (~ (r2_hidden @ X3 @ X5)
% 17.42/17.64          | (r2_hidden @ (k4_tarski @ X1 @ X3) @ 
% 17.42/17.64             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X5)))),
% 17.42/17.64      inference('simplify', [status(thm)], ['17'])).
% 17.42/17.64  thf('45', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.42/17.64         (((k1_tarski @ X0)
% 17.42/17.64            = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 17.42/17.64          | (r2_hidden @ 
% 17.42/17.64             (k4_tarski @ X2 @ 
% 17.42/17.64              (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 17.42/17.64             (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X0))))),
% 17.42/17.64      inference('sup-', [status(thm)], ['43', '44'])).
% 17.42/17.64  thf('46', plain,
% 17.42/17.64      (![X16 : $i, X17 : $i]:
% 17.42/17.64         ((k2_zfmisc_1 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 17.42/17.64           = (k1_tarski @ (k4_tarski @ X16 @ X17)))),
% 17.42/17.64      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 17.42/17.64  thf('47', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.42/17.64         (((k1_tarski @ X0)
% 17.42/17.64            = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 17.42/17.64          | (r2_hidden @ 
% 17.42/17.64             (k4_tarski @ X2 @ 
% 17.42/17.64              (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 17.42/17.64             (k1_tarski @ (k4_tarski @ X2 @ X0))))),
% 17.42/17.64      inference('demod', [status(thm)], ['45', '46'])).
% 17.42/17.64  thf('48', plain,
% 17.42/17.64      (![X27 : $i, X30 : $i, X31 : $i]:
% 17.42/17.64         (((X30) = (k2_relat_1 @ X27))
% 17.42/17.64          | ~ (r2_hidden @ (k4_tarski @ X31 @ (sk_C_1 @ X30 @ X27)) @ X27)
% 17.42/17.64          | ~ (r2_hidden @ (sk_C_1 @ X30 @ X27) @ X30))),
% 17.42/17.64      inference('cnf', [status(esa)], [d5_relat_1])).
% 17.42/17.64  thf('49', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i]:
% 17.42/17.64         (((k1_tarski @ X0)
% 17.42/17.64            = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 17.42/17.64          | ~ (r2_hidden @ 
% 17.42/17.64               (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 17.42/17.64               (k1_tarski @ X0))
% 17.42/17.64          | ((k1_tarski @ X0)
% 17.42/17.64              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 17.42/17.64      inference('sup-', [status(thm)], ['47', '48'])).
% 17.42/17.64  thf('50', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i]:
% 17.42/17.64         (~ (r2_hidden @ 
% 17.42/17.64             (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 17.42/17.64             (k1_tarski @ X0))
% 17.42/17.64          | ((k1_tarski @ X0)
% 17.42/17.64              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 17.42/17.64      inference('simplify', [status(thm)], ['49'])).
% 17.42/17.64  thf('51', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i]:
% 17.42/17.64         ((r2_hidden @ 
% 17.42/17.64           (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 17.42/17.64           (k1_tarski @ X0))
% 17.42/17.64          | ((k1_tarski @ X0)
% 17.42/17.64              = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 17.42/17.64      inference('eq_fact', [status(thm)], ['42'])).
% 17.42/17.64  thf('52', plain,
% 17.42/17.64      (![X0 : $i, X1 : $i]:
% 17.42/17.64         ((k1_tarski @ X0) = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 17.42/17.64      inference('clc', [status(thm)], ['50', '51'])).
% 17.42/17.64  thf('53', plain,
% 17.42/17.64      (![X0 : $i]:
% 17.42/17.64         ((k1_tarski @ X0)
% 17.42/17.64           = (k2_relat_1 @ 
% 17.42/17.64              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ X0))))),
% 17.42/17.64      inference('sup+', [status(thm)], ['37', '52'])).
% 17.42/17.64  thf('54', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_2))),
% 17.42/17.64      inference('sup+', [status(thm)], ['36', '53'])).
% 17.42/17.64  thf('55', plain,
% 17.42/17.64      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A))
% 17.42/17.64        | ((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B)))),
% 17.42/17.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.42/17.64  thf('56', plain,
% 17.42/17.64      ((((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B)))
% 17.42/17.64         <= (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B))))),
% 17.42/17.64      inference('split', [status(esa)], ['55'])).
% 17.42/17.64  thf('57', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 17.42/17.64      inference('sup-', [status(thm)], ['6', '32'])).
% 17.42/17.64  thf('58', plain,
% 17.42/17.64      ((((k1_relat_1 @ sk_C_2) != (k1_tarski @ sk_A)))
% 17.42/17.64         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 17.42/17.64      inference('split', [status(esa)], ['55'])).
% 17.42/17.64  thf('59', plain,
% 17.42/17.64      ((((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_C_2)))
% 17.42/17.64         <= (~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))))),
% 17.42/17.64      inference('sup-', [status(thm)], ['57', '58'])).
% 17.42/17.64  thf('60', plain, ((((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A)))),
% 17.42/17.64      inference('simplify', [status(thm)], ['59'])).
% 17.42/17.64  thf('61', plain,
% 17.42/17.64      (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B))) | 
% 17.42/17.64       ~ (((k1_relat_1 @ sk_C_2) = (k1_tarski @ sk_A)))),
% 17.42/17.64      inference('split', [status(esa)], ['55'])).
% 17.42/17.64  thf('62', plain, (~ (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_B)))),
% 17.42/17.64      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 17.42/17.64  thf('63', plain, (((k2_relat_1 @ sk_C_2) != (k1_tarski @ sk_B))),
% 17.42/17.64      inference('simpl_trail', [status(thm)], ['56', '62'])).
% 17.42/17.64  thf('64', plain, ($false),
% 17.42/17.64      inference('simplify_reflect-', [status(thm)], ['54', '63'])).
% 17.42/17.64  
% 17.42/17.64  % SZS output end Refutation
% 17.42/17.64  
% 17.42/17.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
