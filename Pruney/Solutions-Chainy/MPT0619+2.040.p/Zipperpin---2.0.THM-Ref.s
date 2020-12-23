%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZQ7yLkkihR

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:25 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 813 expanded)
%              Number of leaves         :   19 ( 233 expanded)
%              Depth                    :   26
%              Number of atoms          :  989 (9204 expanded)
%              Number of equality atoms :  112 (1004 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X6 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('9',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( sk_C_1 @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_B ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_C_1 @ sk_B )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('15',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('16',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_B ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_B ) @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_D_1 @ ( sk_C_1 @ sk_B ) @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( sk_C_1 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','24'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
        = sk_A )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_2 @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B )
        = sk_A )
      | ( ( sk_C_2 @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
        = X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','38'])).

thf('40',plain,
    ( ( sk_C_1 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X8 @ X9 ) @ X8 )
      | ( ( sk_C_2 @ X8 @ X9 )
       != ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_B )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_2 @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_B )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ( ( sk_C_2 @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B )
       != ( sk_C_1 @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B )
       != ( sk_C_1 @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( sk_C_1 @ sk_B ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B )
        = sk_A )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,
    ( ( ( sk_D @ ( k2_tarski @ ( sk_C_1 @ sk_B ) @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = sk_A )
    | ( ( sk_D @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = sk_A )
    | ( ( k2_tarski @ ( sk_C_1 @ sk_B ) @ ( sk_C_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = sk_A )
    | ( ( sk_D @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = sk_A )
    | ( ( k1_tarski @ ( sk_C_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( ( k1_tarski @ ( sk_C_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( sk_D @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_C_1 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('60',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_D @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X8 @ X9 ) @ X8 )
      | ( ( sk_C_2 @ X8 @ X9 )
        = ( k1_funct_1 @ X9 @ ( sk_D @ X8 @ X9 ) ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('63',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = ( sk_C_1 @ sk_B ) )
    | ( ( k1_tarski @ ( sk_C_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( sk_C_1 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = ( sk_C_1 @ sk_B ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = ( sk_C_1 @ sk_B ) )
    | ( ( k1_tarski @ ( sk_C_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ( ( k1_tarski @ ( sk_C_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
      = ( sk_C_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('72',plain,
    ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
    = ( sk_C_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X8 @ X9 ) @ X8 )
      | ( ( sk_C_2 @ X8 @ X9 )
       != ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B ) @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( sk_C_1 @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_1 @ sk_B ) ) @ sk_B )
    = ( sk_C_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_C_1 @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( sk_C_1 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79'])).

thf('81',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( sk_C_1 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( sk_C_1 @ sk_B )
     != ( sk_C_1 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('85',plain,(
    ( sk_C_1 @ sk_B )
 != ( sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference(simplify,[status(thm)],['85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZQ7yLkkihR
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 152 iterations in 0.166s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.39/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.39/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.61  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.61  thf(d1_tarski, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.61  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['0'])).
% 0.39/0.61  thf(t14_funct_1, conjecture,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.61       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.39/0.61         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i]:
% 0.39/0.61        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.61          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.39/0.61            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.39/0.61  thf('2', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t18_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.39/0.61            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X6 : $i, X7 : $i]:
% 0.39/0.61         ((r2_hidden @ (sk_C_1 @ X6) @ (k2_relat_1 @ X6))
% 0.39/0.61          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X6))
% 0.39/0.61          | ~ (v1_relat_1 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.39/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.39/0.61          | (r2_hidden @ (sk_C_1 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.39/0.61          | (r2_hidden @ (sk_C_1 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('7', plain, ((r2_hidden @ (sk_C_1 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['1', '6'])).
% 0.39/0.61  thf(d5_funct_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.39/0.61           ( ![C:$i]:
% 0.39/0.61             ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.61               ( ?[D:$i]:
% 0.39/0.61                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.39/0.61                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.39/0.61         (((X11) != (k2_relat_1 @ X9))
% 0.39/0.61          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 0.39/0.61          | ~ (r2_hidden @ X12 @ X11)
% 0.39/0.61          | ~ (v1_funct_1 @ X9)
% 0.39/0.61          | ~ (v1_relat_1 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X9 : $i, X12 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X9)
% 0.39/0.61          | ~ (v1_funct_1 @ X9)
% 0.39/0.61          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.39/0.61          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.39/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      ((((sk_C_1 @ sk_B)
% 0.39/0.61          = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_B) @ sk_B)))
% 0.39/0.61        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['7', '9'])).
% 0.39/0.61  thf('11', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (((sk_C_1 @ sk_B)
% 0.39/0.61         = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_B) @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.39/0.61  thf('14', plain, ((r2_hidden @ (sk_C_1 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['1', '6'])).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.39/0.61         (((X11) != (k2_relat_1 @ X9))
% 0.39/0.61          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 0.39/0.61          | ~ (r2_hidden @ X12 @ X11)
% 0.39/0.61          | ~ (v1_funct_1 @ X9)
% 0.39/0.61          | ~ (v1_relat_1 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X9 : $i, X12 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X9)
% 0.39/0.61          | ~ (v1_funct_1 @ X9)
% 0.39/0.61          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.39/0.61          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_B) @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.39/0.61        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['14', '16'])).
% 0.39/0.61  thf('18', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_B) @ sk_B) @ (k1_tarski @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (![X0 : $i, X3 : $i]:
% 0.39/0.61         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.61  thf('24', plain, (((sk_D_1 @ (sk_C_1 @ sk_B) @ sk_B) = (sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['21', '23'])).
% 0.39/0.61  thf('25', plain, (((sk_C_1 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['13', '24'])).
% 0.39/0.61  thf(t69_enumset1, axiom,
% 0.39/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.61  thf('26', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.61  thf('27', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i]:
% 0.39/0.61         ((r2_hidden @ (sk_C_2 @ X8 @ X9) @ X8)
% 0.39/0.61          | (r2_hidden @ (sk_D @ X8 @ X9) @ (k1_relat_1 @ X9))
% 0.39/0.61          | ((X8) = (k2_relat_1 @ X9))
% 0.39/0.61          | ~ (v1_funct_1 @ X9)
% 0.39/0.61          | ~ (v1_relat_1 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r2_hidden @ (sk_D @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.39/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.39/0.61          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | (r2_hidden @ (sk_C_2 @ X0 @ sk_B) @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.39/0.61  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r2_hidden @ (sk_D @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | (r2_hidden @ (sk_C_2 @ X0 @ sk_B) @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (![X0 : $i, X3 : $i]:
% 0.39/0.61         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r2_hidden @ (sk_C_2 @ X0 @ sk_B) @ X0)
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.61  thf('35', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.61  thf('36', plain,
% 0.39/0.61      (![X0 : $i, X3 : $i]:
% 0.39/0.61         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (((sk_D @ (k2_tarski @ X0 @ X0) @ sk_B) = (sk_A))
% 0.39/0.61          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | ((sk_C_2 @ (k2_tarski @ X0 @ X0) @ sk_B) = (X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['34', '37'])).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (((sk_D @ (k1_tarski @ X0) @ sk_B) = (sk_A))
% 0.39/0.61          | ((sk_C_2 @ (k2_tarski @ X0 @ X0) @ sk_B) = (X0))
% 0.39/0.61          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['26', '38'])).
% 0.39/0.61  thf('40', plain, (((sk_C_1 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['13', '24'])).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((r2_hidden @ (sk_C_2 @ X0 @ sk_B) @ X0)
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.61  thf('42', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         (~ (r2_hidden @ (sk_C_2 @ X8 @ X9) @ X8)
% 0.39/0.61          | ((sk_C_2 @ X8 @ X9) != (k1_funct_1 @ X9 @ X10))
% 0.39/0.61          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.39/0.61          | ((X8) = (k2_relat_1 @ X9))
% 0.39/0.61          | ~ (v1_funct_1 @ X9)
% 0.39/0.61          | ~ (v1_relat_1 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((sk_D @ X0 @ sk_B) = (sk_A))
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.39/0.61          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B))
% 0.39/0.61          | ((sk_C_2 @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ X1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.61  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('46', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('47', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((sk_D @ X0 @ sk_B) = (sk_A))
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A))
% 0.39/0.61          | ((sk_C_2 @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ X1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.39/0.61  thf('48', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((sk_C_2 @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ X1))
% 0.39/0.61          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A))
% 0.39/0.61          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.61          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_C_2 @ X0 @ sk_B) != (sk_C_1 @ sk_B))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B))
% 0.39/0.62          | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['40', '48'])).
% 0.39/0.62  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_C_2 @ X0 @ sk_B) != (sk_C_1 @ sk_B))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['49', '50'])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((X0) != (sk_C_1 @ sk_B))
% 0.39/0.62          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B))
% 0.39/0.62          | ((sk_D @ (k1_tarski @ X0) @ sk_B) = (sk_A))
% 0.39/0.62          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B))
% 0.39/0.62          | ((sk_D @ (k2_tarski @ X0 @ X0) @ sk_B) = (sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['39', '51'])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      ((((sk_D @ (k2_tarski @ (sk_C_1 @ sk_B) @ (sk_C_1 @ sk_B)) @ sk_B)
% 0.39/0.62          = (sk_A))
% 0.39/0.62        | ((sk_D @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.39/0.62        | ((k2_tarski @ (sk_C_1 @ sk_B) @ (sk_C_1 @ sk_B))
% 0.39/0.62            = (k2_relat_1 @ sk_B)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['52'])).
% 0.39/0.62  thf('54', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.62  thf('55', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      ((((sk_D @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.39/0.62        | ((sk_D @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.39/0.62        | ((k1_tarski @ (sk_C_1 @ sk_B)) = (k2_relat_1 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      ((((k1_tarski @ (sk_C_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.39/0.62        | ((sk_D @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['56'])).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('59', plain, (((sk_C_1 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['13', '24'])).
% 0.39/0.62  thf('60', plain, (((k2_relat_1 @ sk_B) != (k1_tarski @ (sk_C_1 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('61', plain, (((sk_D @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['57', '60'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((r2_hidden @ (sk_C_2 @ X8 @ X9) @ X8)
% 0.39/0.62          | ((sk_C_2 @ X8 @ X9) = (k1_funct_1 @ X9 @ (sk_D @ X8 @ X9)))
% 0.39/0.62          | ((X8) = (k2_relat_1 @ X9))
% 0.39/0.62          | ~ (v1_funct_1 @ X9)
% 0.39/0.62          | ~ (v1_relat_1 @ X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      (![X0 : $i, X3 : $i]:
% 0.39/0.62         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X1)
% 0.39/0.62          | ~ (v1_funct_1 @ X1)
% 0.39/0.62          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.39/0.62          | ((sk_C_2 @ (k1_tarski @ X0) @ X1)
% 0.39/0.62              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 0.39/0.62          | ((sk_C_2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      ((((sk_C_2 @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B)
% 0.39/0.62          = (k1_funct_1 @ sk_B @ sk_A))
% 0.39/0.62        | ((sk_C_2 @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_C_1 @ sk_B))
% 0.39/0.62        | ((k1_tarski @ (sk_C_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['61', '64'])).
% 0.39/0.62  thf('66', plain, (((sk_C_1 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['13', '24'])).
% 0.39/0.62  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      ((((sk_C_2 @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_C_1 @ sk_B))
% 0.39/0.62        | ((sk_C_2 @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_C_1 @ sk_B))
% 0.39/0.62        | ((k1_tarski @ (sk_C_1 @ sk_B)) = (k2_relat_1 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      ((((k1_tarski @ (sk_C_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.39/0.62        | ((sk_C_2 @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_C_1 @ sk_B)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['69'])).
% 0.39/0.62  thf('71', plain, (((k2_relat_1 @ sk_B) != (k1_tarski @ (sk_C_1 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      (((sk_C_2 @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_C_1 @ sk_B))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.62         (~ (r2_hidden @ (sk_C_2 @ X8 @ X9) @ X8)
% 0.39/0.62          | ((sk_C_2 @ X8 @ X9) != (k1_funct_1 @ X9 @ X10))
% 0.39/0.62          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.39/0.62          | ((X8) = (k2_relat_1 @ X9))
% 0.39/0.62          | ~ (v1_funct_1 @ X9)
% 0.39/0.62          | ~ (v1_relat_1 @ X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ (sk_C_1 @ sk_B) @ (k1_tarski @ (sk_C_1 @ sk_B)))
% 0.39/0.62          | ~ (v1_relat_1 @ sk_B)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.62          | ((k1_tarski @ (sk_C_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.39/0.62          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.39/0.62          | ((sk_C_2 @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B)
% 0.39/0.62              != (k1_funct_1 @ sk_B @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.39/0.62  thf('75', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.39/0.62  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('77', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('78', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('79', plain,
% 0.39/0.62      (((sk_C_2 @ (k1_tarski @ (sk_C_1 @ sk_B)) @ sk_B) = (sk_C_1 @ sk_B))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_tarski @ (sk_C_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.39/0.62          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.39/0.62          | ((sk_C_1 @ sk_B) != (k1_funct_1 @ sk_B @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['74', '75', '76', '77', '78', '79'])).
% 0.39/0.62  thf('81', plain, (((k2_relat_1 @ sk_B) != (k1_tarski @ (sk_C_1 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.39/0.62          | ((sk_C_1 @ sk_B) != (k1_funct_1 @ sk_B @ X0)))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      ((((sk_C_1 @ sk_B) != (sk_C_1 @ sk_B))
% 0.39/0.62        | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['25', '82'])).
% 0.39/0.62  thf('84', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.39/0.62  thf('85', plain, (((sk_C_1 @ sk_B) != (sk_C_1 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['83', '84'])).
% 0.39/0.62  thf('86', plain, ($false), inference('simplify', [status(thm)], ['85'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
