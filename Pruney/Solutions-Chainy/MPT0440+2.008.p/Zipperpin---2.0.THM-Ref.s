%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HwTLCEUfWB

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:43 EST 2020

% Result     : Theorem 7.65s
% Output     : Refutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 882 expanded)
%              Number of leaves         :   23 ( 243 expanded)
%              Depth                    :   26
%              Number of atoms          :  909 (9686 expanded)
%              Number of equality atoms :  105 (1032 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('5',plain,(
    ! [X60: $i,X63: $i] :
      ( ( X63
        = ( k2_relat_1 @ X60 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X63 @ X60 ) @ ( sk_C_2 @ X63 @ X60 ) ) @ X60 )
      | ( r2_hidden @ ( sk_C_2 @ X63 @ X60 ) @ X63 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k4_tarski @ ( sk_D_3 @ X1 @ ( k1_tarski @ X0 ) ) @ ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

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
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('14',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X33 ) @ ( sk_E @ X33 ) )
        = X33 )
      | ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_tarski @ ( sk_D @ ( k4_tarski @ X1 @ X0 ) ) @ ( sk_E @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k4_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_tarski @ ( sk_D @ ( k4_tarski @ X1 @ X0 ) ) @ ( sk_E @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k4_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X37 = X36 )
      | ~ ( r2_hidden @ ( k4_tarski @ X37 @ X38 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X36 ) @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X3 ) @ X2 ) )
      | ( ( sk_D @ ( k4_tarski @ X1 @ X0 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_tarski @ X1 @ ( sk_E @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k4_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X43 = X44 )
      | ~ ( r2_hidden @ ( k4_tarski @ X41 @ X43 ) @ ( k2_zfmisc_1 @ X42 @ ( k1_tarski @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X2 ) ) )
      | ( ( sk_E @ ( k4_tarski @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_E @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_E @ X0 )
        = ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( X1
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_E @ X1 )
        = ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_E @ X0 )
       != X1 )
      | ( ( sk_C_2 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k1_tarski @ X1 )
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_E @ X0 ) )
        = ( k2_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ ( sk_E @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( sk_E @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ ( sk_E @ ( k4_tarski @ sk_A @ sk_B ) ) ) @ sk_C_3 )
      = ( sk_E @ ( k4_tarski @ sk_A @ sk_B ) ) )
    | ( ( k1_tarski @ ( sk_E @ ( k4_tarski @ sk_A @ sk_B ) ) )
      = ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['4','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_E @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_E @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_E @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('34',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
      = sk_B )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['0','2'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('39',plain,(
    ! [X53: $i,X56: $i] :
      ( ( X56
        = ( k1_relat_1 @ X53 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X56 @ X53 ) @ ( sk_D_1 @ X56 @ X53 ) ) @ X53 )
      | ( r2_hidden @ ( sk_C_1 @ X56 @ X53 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('40',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_3 )
      | ( X0
        = ( k4_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D_1 @ X0 @ sk_C_3 ) )
        = ( k4_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k4_tarski @ sk_A @ sk_B ) )
        = ( sk_C_1 @ X0 @ sk_C_3 ) )
      | ( X0
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( sk_C_1 @ X0 @ sk_C_3 ) )
      | ( X0
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( sk_A
        = ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('53',plain,(
    ! [X53: $i,X56: $i,X57: $i] :
      ( ( X56
        = ( k1_relat_1 @ X53 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X56 @ X53 ) @ X57 ) @ X53 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X56 @ X53 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['38','59'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['36'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['36'])).

thf('65',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['37','65'])).

thf('67',plain,
    ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['35','66'])).

thf('68',plain,(
    ! [X60: $i,X63: $i,X64: $i] :
      ( ( X63
        = ( k2_relat_1 @ X60 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X64 @ ( sk_C_2 @ X63 @ X60 ) ) @ X60 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X63 @ X60 ) @ X63 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['35','66'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['37','65'])).

thf('74',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HwTLCEUfWB
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.65/7.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.65/7.83  % Solved by: fo/fo7.sh
% 7.65/7.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.65/7.83  % done 5017 iterations in 7.374s
% 7.65/7.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.65/7.83  % SZS output start Refutation
% 7.65/7.83  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 7.65/7.83  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 7.65/7.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.65/7.83  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 7.65/7.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.65/7.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.65/7.83  thf(sk_C_3_type, type, sk_C_3: $i).
% 7.65/7.83  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 7.65/7.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.65/7.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.65/7.83  thf(sk_E_type, type, sk_E: $i > $i).
% 7.65/7.83  thf(sk_B_type, type, sk_B: $i).
% 7.65/7.83  thf(sk_A_type, type, sk_A: $i).
% 7.65/7.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.65/7.83  thf(sk_D_type, type, sk_D: $i > $i).
% 7.65/7.83  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 7.65/7.83  thf(t23_relat_1, conjecture,
% 7.65/7.83    (![A:$i,B:$i,C:$i]:
% 7.65/7.83     ( ( v1_relat_1 @ C ) =>
% 7.65/7.83       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 7.65/7.83         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 7.65/7.83           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 7.65/7.83  thf(zf_stmt_0, negated_conjecture,
% 7.65/7.83    (~( ![A:$i,B:$i,C:$i]:
% 7.65/7.83        ( ( v1_relat_1 @ C ) =>
% 7.65/7.83          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 7.65/7.83            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 7.65/7.83              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 7.65/7.83    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 7.65/7.83  thf('0', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 7.65/7.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.65/7.83  thf(d1_tarski, axiom,
% 7.65/7.83    (![A:$i,B:$i]:
% 7.65/7.83     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 7.65/7.83       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 7.65/7.83  thf('1', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.65/7.83         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 7.65/7.83      inference('cnf', [status(esa)], [d1_tarski])).
% 7.65/7.83  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.65/7.83      inference('simplify', [status(thm)], ['1'])).
% 7.65/7.83  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 7.65/7.83      inference('sup+', [status(thm)], ['0', '2'])).
% 7.65/7.83  thf('4', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 7.65/7.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.65/7.83  thf(d5_relat_1, axiom,
% 7.65/7.83    (![A:$i,B:$i]:
% 7.65/7.83     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 7.65/7.83       ( ![C:$i]:
% 7.65/7.83         ( ( r2_hidden @ C @ B ) <=>
% 7.65/7.83           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 7.65/7.83  thf('5', plain,
% 7.65/7.83      (![X60 : $i, X63 : $i]:
% 7.65/7.83         (((X63) = (k2_relat_1 @ X60))
% 7.65/7.83          | (r2_hidden @ 
% 7.65/7.83             (k4_tarski @ (sk_D_3 @ X63 @ X60) @ (sk_C_2 @ X63 @ X60)) @ X60)
% 7.65/7.83          | (r2_hidden @ (sk_C_2 @ X63 @ X60) @ X63))),
% 7.65/7.83      inference('cnf', [status(esa)], [d5_relat_1])).
% 7.65/7.83  thf('6', plain,
% 7.65/7.83      (![X0 : $i, X2 : $i, X3 : $i]:
% 7.65/7.83         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 7.65/7.83      inference('cnf', [status(esa)], [d1_tarski])).
% 7.65/7.83  thf('7', plain,
% 7.65/7.83      (![X0 : $i, X3 : $i]:
% 7.65/7.83         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['6'])).
% 7.65/7.83  thf('8', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         ((r2_hidden @ (sk_C_2 @ X1 @ (k1_tarski @ X0)) @ X1)
% 7.65/7.83          | ((X1) = (k2_relat_1 @ (k1_tarski @ X0)))
% 7.65/7.83          | ((k4_tarski @ (sk_D_3 @ X1 @ (k1_tarski @ X0)) @ 
% 7.65/7.83              (sk_C_2 @ X1 @ (k1_tarski @ X0))) = (X0)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['5', '7'])).
% 7.65/7.83  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.65/7.83      inference('simplify', [status(thm)], ['1'])).
% 7.65/7.83  thf(t128_zfmisc_1, axiom,
% 7.65/7.83    (![A:$i,B:$i,C:$i,D:$i]:
% 7.65/7.83     ( ( r2_hidden @
% 7.65/7.83         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 7.65/7.83       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 7.65/7.83  thf('10', plain,
% 7.65/7.83      (![X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 7.65/7.83         ((r2_hidden @ (k4_tarski @ X37 @ X38) @ 
% 7.65/7.83           (k2_zfmisc_1 @ (k1_tarski @ X36) @ X40))
% 7.65/7.83          | ~ (r2_hidden @ X38 @ X40)
% 7.65/7.83          | ((X37) != (X36)))),
% 7.65/7.83      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 7.65/7.83  thf('11', plain,
% 7.65/7.83      (![X36 : $i, X38 : $i, X40 : $i]:
% 7.65/7.83         (~ (r2_hidden @ X38 @ X40)
% 7.65/7.83          | (r2_hidden @ (k4_tarski @ X36 @ X38) @ 
% 7.65/7.83             (k2_zfmisc_1 @ (k1_tarski @ X36) @ X40)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['10'])).
% 7.65/7.83  thf('12', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 7.65/7.83          (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['9', '11'])).
% 7.65/7.83  thf('13', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 7.65/7.83          (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['9', '11'])).
% 7.65/7.83  thf(l139_zfmisc_1, axiom,
% 7.65/7.83    (![A:$i,B:$i,C:$i]:
% 7.65/7.83     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 7.65/7.83          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 7.65/7.83  thf('14', plain,
% 7.65/7.83      (![X33 : $i, X34 : $i, X35 : $i]:
% 7.65/7.83         (((k4_tarski @ (sk_D @ X33) @ (sk_E @ X33)) = (X33))
% 7.65/7.83          | ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 7.65/7.83      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 7.65/7.83  thf('15', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         ((k4_tarski @ (sk_D @ (k4_tarski @ X1 @ X0)) @ 
% 7.65/7.83           (sk_E @ (k4_tarski @ X1 @ X0))) = (k4_tarski @ X1 @ X0))),
% 7.65/7.83      inference('sup-', [status(thm)], ['13', '14'])).
% 7.65/7.83  thf('16', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 7.65/7.83          (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['9', '11'])).
% 7.65/7.83  thf('17', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         ((k4_tarski @ (sk_D @ (k4_tarski @ X1 @ X0)) @ 
% 7.65/7.83           (sk_E @ (k4_tarski @ X1 @ X0))) = (k4_tarski @ X1 @ X0))),
% 7.65/7.83      inference('sup-', [status(thm)], ['13', '14'])).
% 7.65/7.83  thf('18', plain,
% 7.65/7.83      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 7.65/7.83         (((X37) = (X36))
% 7.65/7.83          | ~ (r2_hidden @ (k4_tarski @ X37 @ X38) @ 
% 7.65/7.83               (k2_zfmisc_1 @ (k1_tarski @ X36) @ X39)))),
% 7.65/7.83      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 7.65/7.83  thf('19', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.65/7.83         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 7.65/7.83             (k2_zfmisc_1 @ (k1_tarski @ X3) @ X2))
% 7.65/7.83          | ((sk_D @ (k4_tarski @ X1 @ X0)) = (X3)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['17', '18'])).
% 7.65/7.83  thf('20', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]: ((sk_D @ (k4_tarski @ X1 @ X0)) = (X1))),
% 7.65/7.83      inference('sup-', [status(thm)], ['16', '19'])).
% 7.65/7.83  thf('21', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         ((k4_tarski @ X1 @ (sk_E @ (k4_tarski @ X1 @ X0)))
% 7.65/7.83           = (k4_tarski @ X1 @ X0))),
% 7.65/7.83      inference('demod', [status(thm)], ['15', '20'])).
% 7.65/7.83  thf(t129_zfmisc_1, axiom,
% 7.65/7.83    (![A:$i,B:$i,C:$i,D:$i]:
% 7.65/7.83     ( ( r2_hidden @
% 7.65/7.83         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 7.65/7.83       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 7.65/7.83  thf('22', plain,
% 7.65/7.83      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 7.65/7.83         (((X43) = (X44))
% 7.65/7.83          | ~ (r2_hidden @ (k4_tarski @ X41 @ X43) @ 
% 7.65/7.83               (k2_zfmisc_1 @ X42 @ (k1_tarski @ X44))))),
% 7.65/7.83      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 7.65/7.83  thf('23', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.65/7.83         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 7.65/7.83             (k2_zfmisc_1 @ X3 @ (k1_tarski @ X2)))
% 7.65/7.83          | ((sk_E @ (k4_tarski @ X1 @ X0)) = (X2)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['21', '22'])).
% 7.65/7.83  thf('24', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]: ((sk_E @ (k4_tarski @ X1 @ X0)) = (X0))),
% 7.65/7.83      inference('sup-', [status(thm)], ['12', '23'])).
% 7.65/7.83  thf('25', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         (((sk_E @ X0) = (sk_C_2 @ X1 @ (k1_tarski @ X0)))
% 7.65/7.83          | ((X1) = (k2_relat_1 @ (k1_tarski @ X0)))
% 7.65/7.83          | (r2_hidden @ (sk_C_2 @ X1 @ (k1_tarski @ X0)) @ X1))),
% 7.65/7.83      inference('sup+', [status(thm)], ['8', '24'])).
% 7.65/7.83  thf('26', plain,
% 7.65/7.83      (![X0 : $i, X3 : $i]:
% 7.65/7.83         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['6'])).
% 7.65/7.83  thf('27', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         (((k1_tarski @ X0) = (k2_relat_1 @ (k1_tarski @ X1)))
% 7.65/7.83          | ((sk_E @ X1) = (sk_C_2 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 7.65/7.83          | ((sk_C_2 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) = (X0)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['25', '26'])).
% 7.65/7.83  thf('28', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]:
% 7.65/7.83         (((sk_E @ X0) != (X1))
% 7.65/7.83          | ((sk_C_2 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) = (X1))
% 7.65/7.83          | ((k1_tarski @ X1) = (k2_relat_1 @ (k1_tarski @ X0))))),
% 7.65/7.83      inference('eq_fact', [status(thm)], ['27'])).
% 7.65/7.83  thf('29', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (((k1_tarski @ (sk_E @ X0)) = (k2_relat_1 @ (k1_tarski @ X0)))
% 7.65/7.83          | ((sk_C_2 @ (k1_tarski @ (sk_E @ X0)) @ (k1_tarski @ X0))
% 7.65/7.83              = (sk_E @ X0)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['28'])).
% 7.65/7.83  thf('30', plain,
% 7.65/7.83      ((((sk_C_2 @ (k1_tarski @ (sk_E @ (k4_tarski @ sk_A @ sk_B))) @ sk_C_3)
% 7.65/7.83          = (sk_E @ (k4_tarski @ sk_A @ sk_B)))
% 7.65/7.83        | ((k1_tarski @ (sk_E @ (k4_tarski @ sk_A @ sk_B)))
% 7.65/7.83            = (k2_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))))),
% 7.65/7.83      inference('sup+', [status(thm)], ['4', '29'])).
% 7.65/7.83  thf('31', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]: ((sk_E @ (k4_tarski @ X1 @ X0)) = (X0))),
% 7.65/7.83      inference('sup-', [status(thm)], ['12', '23'])).
% 7.65/7.83  thf('32', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]: ((sk_E @ (k4_tarski @ X1 @ X0)) = (X0))),
% 7.65/7.83      inference('sup-', [status(thm)], ['12', '23'])).
% 7.65/7.83  thf('33', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]: ((sk_E @ (k4_tarski @ X1 @ X0)) = (X0))),
% 7.65/7.83      inference('sup-', [status(thm)], ['12', '23'])).
% 7.65/7.83  thf('34', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 7.65/7.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.65/7.83  thf('35', plain,
% 7.65/7.83      ((((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))
% 7.65/7.83        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 7.65/7.83      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 7.65/7.83  thf('36', plain,
% 7.65/7.83      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))
% 7.65/7.83        | ((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))),
% 7.65/7.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.65/7.83  thf('37', plain,
% 7.65/7.83      ((((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))
% 7.65/7.83         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 7.65/7.83      inference('split', [status(esa)], ['36'])).
% 7.65/7.83  thf('38', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 7.65/7.83      inference('sup+', [status(thm)], ['0', '2'])).
% 7.65/7.83  thf(d4_relat_1, axiom,
% 7.65/7.83    (![A:$i,B:$i]:
% 7.65/7.83     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 7.65/7.83       ( ![C:$i]:
% 7.65/7.83         ( ( r2_hidden @ C @ B ) <=>
% 7.65/7.83           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 7.65/7.83  thf('39', plain,
% 7.65/7.83      (![X53 : $i, X56 : $i]:
% 7.65/7.83         (((X56) = (k1_relat_1 @ X53))
% 7.65/7.83          | (r2_hidden @ 
% 7.65/7.83             (k4_tarski @ (sk_C_1 @ X56 @ X53) @ (sk_D_1 @ X56 @ X53)) @ X53)
% 7.65/7.83          | (r2_hidden @ (sk_C_1 @ X56 @ X53) @ X56))),
% 7.65/7.83      inference('cnf', [status(esa)], [d4_relat_1])).
% 7.65/7.83  thf('40', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 7.65/7.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.65/7.83  thf('41', plain,
% 7.65/7.83      (![X0 : $i, X3 : $i]:
% 7.65/7.83         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['6'])).
% 7.65/7.83  thf('42', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (~ (r2_hidden @ X0 @ sk_C_3) | ((X0) = (k4_tarski @ sk_A @ sk_B)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['40', '41'])).
% 7.65/7.83  thf('43', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X0)
% 7.65/7.83          | ((X0) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83          | ((k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D_1 @ X0 @ sk_C_3))
% 7.65/7.83              = (k4_tarski @ sk_A @ sk_B)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['39', '42'])).
% 7.65/7.83  thf('44', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]: ((sk_D @ (k4_tarski @ X1 @ X0)) = (X1))),
% 7.65/7.83      inference('sup-', [status(thm)], ['16', '19'])).
% 7.65/7.83  thf('45', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (((sk_D @ (k4_tarski @ sk_A @ sk_B)) = (sk_C_1 @ X0 @ sk_C_3))
% 7.65/7.83          | ((X0) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X0))),
% 7.65/7.83      inference('sup+', [status(thm)], ['43', '44'])).
% 7.65/7.83  thf('46', plain,
% 7.65/7.83      (![X0 : $i, X1 : $i]: ((sk_D @ (k4_tarski @ X1 @ X0)) = (X1))),
% 7.65/7.83      inference('sup-', [status(thm)], ['16', '19'])).
% 7.65/7.83  thf('47', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (((sk_A) = (sk_C_1 @ X0 @ sk_C_3))
% 7.65/7.83          | ((X0) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X0))),
% 7.65/7.83      inference('demod', [status(thm)], ['45', '46'])).
% 7.65/7.83  thf('48', plain,
% 7.65/7.83      (![X0 : $i, X3 : $i]:
% 7.65/7.83         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['6'])).
% 7.65/7.83  thf('49', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83          | ((sk_A) = (sk_C_1 @ (k1_tarski @ X0) @ sk_C_3))
% 7.65/7.83          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['47', '48'])).
% 7.65/7.83  thf('50', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (((sk_A) != (X0))
% 7.65/7.83          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0))
% 7.65/7.83          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3)))),
% 7.65/7.83      inference('eq_fact', [status(thm)], ['49'])).
% 7.65/7.83  thf('51', plain,
% 7.65/7.83      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['50'])).
% 7.65/7.83  thf('52', plain,
% 7.65/7.83      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['50'])).
% 7.65/7.83  thf('53', plain,
% 7.65/7.83      (![X53 : $i, X56 : $i, X57 : $i]:
% 7.65/7.83         (((X56) = (k1_relat_1 @ X53))
% 7.65/7.83          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X56 @ X53) @ X57) @ X53)
% 7.65/7.83          | ~ (r2_hidden @ (sk_C_1 @ X56 @ X53) @ X56))),
% 7.65/7.83      inference('cnf', [status(esa)], [d4_relat_1])).
% 7.65/7.83  thf('54', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 7.65/7.83          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83          | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 7.65/7.83               (k1_tarski @ sk_A))
% 7.65/7.83          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['52', '53'])).
% 7.65/7.83  thf('55', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 7.65/7.83             (k1_tarski @ sk_A))
% 7.65/7.83          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3))),
% 7.65/7.83      inference('simplify', [status(thm)], ['54'])).
% 7.65/7.83  thf('56', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 7.65/7.83          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 7.65/7.83          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['51', '55'])).
% 7.65/7.83  thf('57', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.65/7.83      inference('simplify', [status(thm)], ['1'])).
% 7.65/7.83  thf('58', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 7.65/7.83          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 7.65/7.83          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 7.65/7.83      inference('demod', [status(thm)], ['56', '57'])).
% 7.65/7.83  thf('59', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 7.65/7.83          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['58'])).
% 7.65/7.83  thf('60', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 7.65/7.83      inference('sup-', [status(thm)], ['38', '59'])).
% 7.65/7.83  thf('61', plain,
% 7.65/7.83      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A)))
% 7.65/7.83         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 7.65/7.83      inference('split', [status(esa)], ['36'])).
% 7.65/7.83  thf('62', plain,
% 7.65/7.83      ((((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_C_3)))
% 7.65/7.83         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 7.65/7.83      inference('sup-', [status(thm)], ['60', '61'])).
% 7.65/7.83  thf('63', plain, ((((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 7.65/7.83      inference('simplify', [status(thm)], ['62'])).
% 7.65/7.83  thf('64', plain,
% 7.65/7.83      (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))) | 
% 7.65/7.83       ~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 7.65/7.83      inference('split', [status(esa)], ['36'])).
% 7.65/7.83  thf('65', plain, (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 7.65/7.83      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 7.65/7.83  thf('66', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 7.65/7.83      inference('simpl_trail', [status(thm)], ['37', '65'])).
% 7.65/7.83  thf('67', plain, (((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))),
% 7.65/7.83      inference('simplify_reflect-', [status(thm)], ['35', '66'])).
% 7.65/7.83  thf('68', plain,
% 7.65/7.83      (![X60 : $i, X63 : $i, X64 : $i]:
% 7.65/7.83         (((X63) = (k2_relat_1 @ X60))
% 7.65/7.83          | ~ (r2_hidden @ (k4_tarski @ X64 @ (sk_C_2 @ X63 @ X60)) @ X60)
% 7.65/7.83          | ~ (r2_hidden @ (sk_C_2 @ X63 @ X60) @ X63))),
% 7.65/7.83      inference('cnf', [status(esa)], [d5_relat_1])).
% 7.65/7.83  thf('69', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 7.65/7.83          | ~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 7.65/7.83               (k1_tarski @ sk_B))
% 7.65/7.83          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 7.65/7.83      inference('sup-', [status(thm)], ['67', '68'])).
% 7.65/7.83  thf('70', plain, (((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))),
% 7.65/7.83      inference('simplify_reflect-', [status(thm)], ['35', '66'])).
% 7.65/7.83  thf('71', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.65/7.83      inference('simplify', [status(thm)], ['1'])).
% 7.65/7.83  thf('72', plain,
% 7.65/7.83      (![X0 : $i]:
% 7.65/7.83         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 7.65/7.83          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 7.65/7.83      inference('demod', [status(thm)], ['69', '70', '71'])).
% 7.65/7.83  thf('73', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 7.65/7.83      inference('simpl_trail', [status(thm)], ['37', '65'])).
% 7.65/7.83  thf('74', plain,
% 7.65/7.83      (![X0 : $i]: ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)),
% 7.65/7.83      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 7.65/7.83  thf('75', plain, ($false), inference('sup-', [status(thm)], ['3', '74'])).
% 7.65/7.83  
% 7.65/7.83  % SZS output end Refutation
% 7.65/7.83  
% 7.65/7.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
