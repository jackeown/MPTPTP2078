%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TBOxxF891l

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:59 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 242 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   29
%              Number of atoms          : 1199 (2510 expanded)
%              Number of equality atoms :   68 ( 147 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf(t117_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k11_relat_1 @ B @ A )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_funct_1])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( X33
       != ( k1_funct_1 @ X32 @ X31 ) )
      | ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ( r2_hidden @ ( k4_tarski @ X31 @ ( k1_funct_1 @ X32 @ X31 ) ) @ X32 )
      | ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X30 @ X28 ) @ X29 )
      | ( r2_hidden @ X28 @ ( k11_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 @ X0 @ X0 )
      | ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','40'])).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k11_relat_1 @ X29 @ X30 ) )
      | ( r2_hidden @ ( k4_tarski @ X30 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 @ X0 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 @ X0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ X1 @ X1 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('56',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k11_relat_1 @ X29 @ X30 ) )
      | ( r2_hidden @ ( k4_tarski @ X30 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ X32 )
      | ( X33
        = ( k1_funct_1 @ X32 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('63',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B )
      | ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ X32 )
      | ( X33
        = ( k1_funct_1 @ X32 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','65'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('81',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X22 ) @ X22 )
      | ( X22
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k11_relat_1 @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( ( sk_C_1 @ X23 @ X22 )
       != X23 )
      | ( X22
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('91',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k11_relat_1 @ X24 @ X25 )
        = ( k9_relat_1 @ X24 @ ( k1_tarski @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('92',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k9_relat_1 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','65'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TBOxxF891l
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:12:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.80/1.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.80/1.99  % Solved by: fo/fo7.sh
% 1.80/1.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/1.99  % done 2385 iterations in 1.536s
% 1.80/1.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.80/1.99  % SZS output start Refutation
% 1.80/1.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.80/1.99  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.80/1.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/1.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.80/1.99  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.80/1.99  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.80/1.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.80/1.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.80/1.99  thf(sk_B_type, type, sk_B: $i).
% 1.80/1.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.80/1.99  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.80/1.99  thf(sk_A_type, type, sk_A: $i).
% 1.80/1.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.80/1.99  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.80/1.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.80/1.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.80/1.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.80/1.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.80/1.99  thf(t69_enumset1, axiom,
% 1.80/1.99    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.80/1.99  thf('0', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.80/1.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.80/1.99  thf(t70_enumset1, axiom,
% 1.80/1.99    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.80/1.99  thf('1', plain,
% 1.80/1.99      (![X17 : $i, X18 : $i]:
% 1.80/1.99         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.80/1.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.80/1.99  thf(d1_enumset1, axiom,
% 1.80/1.99    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/1.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.80/1.99       ( ![E:$i]:
% 1.80/1.99         ( ( r2_hidden @ E @ D ) <=>
% 1.80/1.99           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.80/1.99  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.80/1.99  thf(zf_stmt_1, axiom,
% 1.80/1.99    (![E:$i,C:$i,B:$i,A:$i]:
% 1.80/1.99     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.80/1.99       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.80/1.99  thf(zf_stmt_2, axiom,
% 1.80/1.99    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/1.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.80/1.99       ( ![E:$i]:
% 1.80/1.99         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.80/1.99  thf('2', plain,
% 1.80/1.99      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.80/1.99         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 1.80/1.99          | (r2_hidden @ X9 @ X13)
% 1.80/1.99          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.80/1.99  thf('3', plain,
% 1.80/1.99      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.80/1.99         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 1.80/1.99          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 1.80/1.99      inference('simplify', [status(thm)], ['2'])).
% 1.80/1.99  thf('4', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.80/1.99          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.80/1.99      inference('sup+', [status(thm)], ['1', '3'])).
% 1.80/1.99  thf('5', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.80/1.99          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.80/1.99      inference('sup+', [status(thm)], ['0', '4'])).
% 1.80/1.99  thf('6', plain,
% 1.80/1.99      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.80/1.99         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 1.80/1.99          | ((X5) = (X6))
% 1.80/1.99          | ((X5) = (X7))
% 1.80/1.99          | ((X5) = (X8)))),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.80/1.99  thf(t3_xboole_0, axiom,
% 1.80/1.99    (![A:$i,B:$i]:
% 1.80/1.99     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.80/1.99            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.80/1.99       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.80/1.99            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.80/1.99  thf('7', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('8', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.80/1.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.80/1.99  thf('9', plain,
% 1.80/1.99      (![X17 : $i, X18 : $i]:
% 1.80/1.99         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.80/1.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.80/1.99  thf('10', plain,
% 1.80/1.99      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X14 @ X13)
% 1.80/1.99          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 1.80/1.99          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.80/1.99  thf('11', plain,
% 1.80/1.99      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 1.80/1.99         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 1.80/1.99          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.80/1.99      inference('simplify', [status(thm)], ['10'])).
% 1.80/1.99  thf('12', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.80/1.99          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.80/1.99      inference('sup-', [status(thm)], ['9', '11'])).
% 1.80/1.99  thf('13', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.80/1.99          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.80/1.99      inference('sup-', [status(thm)], ['8', '12'])).
% 1.80/1.99  thf('14', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.80/1.99          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.80/1.99      inference('sup-', [status(thm)], ['7', '13'])).
% 1.80/1.99  thf('15', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.80/1.99          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.80/1.99          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.80/1.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.80/1.99      inference('sup-', [status(thm)], ['6', '14'])).
% 1.80/1.99  thf('16', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.80/1.99          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.80/1.99      inference('simplify', [status(thm)], ['15'])).
% 1.80/1.99  thf('17', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('18', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r2_hidden @ X0 @ X1)
% 1.80/1.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.80/1.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.80/1.99      inference('sup+', [status(thm)], ['16', '17'])).
% 1.80/1.99  thf('19', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.80/1.99      inference('simplify', [status(thm)], ['18'])).
% 1.80/1.99  thf('20', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('21', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('22', plain,
% 1.80/1.99      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X2 @ X0)
% 1.80/1.99          | ~ (r2_hidden @ X2 @ X3)
% 1.80/1.99          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('23', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X1 @ X0)
% 1.80/1.99          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.80/1.99          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.80/1.99      inference('sup-', [status(thm)], ['21', '22'])).
% 1.80/1.99  thf('24', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X0 @ X1)
% 1.80/1.99          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.80/1.99          | (r1_xboole_0 @ X0 @ X1))),
% 1.80/1.99      inference('sup-', [status(thm)], ['20', '23'])).
% 1.80/1.99  thf('25', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.80/1.99      inference('simplify', [status(thm)], ['24'])).
% 1.80/1.99  thf('26', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['19', '25'])).
% 1.80/1.99  thf(t117_funct_1, conjecture,
% 1.80/1.99    (![A:$i,B:$i]:
% 1.80/1.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.80/1.99       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.80/1.99         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.80/1.99  thf(zf_stmt_3, negated_conjecture,
% 1.80/1.99    (~( ![A:$i,B:$i]:
% 1.80/1.99        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.80/1.99          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.80/1.99            ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 1.80/1.99    inference('cnf.neg', [status(esa)], [t117_funct_1])).
% 1.80/1.99  thf('27', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf(t8_funct_1, axiom,
% 1.80/1.99    (![A:$i,B:$i,C:$i]:
% 1.80/1.99     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.80/1.99       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.80/1.99         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.80/1.99           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.80/1.99  thf('28', plain,
% 1.80/1.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 1.80/1.99          | ((X33) != (k1_funct_1 @ X32 @ X31))
% 1.80/1.99          | (r2_hidden @ (k4_tarski @ X31 @ X33) @ X32)
% 1.80/1.99          | ~ (v1_funct_1 @ X32)
% 1.80/1.99          | ~ (v1_relat_1 @ X32))),
% 1.80/1.99      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.80/1.99  thf('29', plain,
% 1.80/1.99      (![X31 : $i, X32 : $i]:
% 1.80/1.99         (~ (v1_relat_1 @ X32)
% 1.80/1.99          | ~ (v1_funct_1 @ X32)
% 1.80/1.99          | (r2_hidden @ (k4_tarski @ X31 @ (k1_funct_1 @ X32 @ X31)) @ X32)
% 1.80/1.99          | ~ (r2_hidden @ X31 @ (k1_relat_1 @ X32)))),
% 1.80/1.99      inference('simplify', [status(thm)], ['28'])).
% 1.80/1.99  thf('30', plain,
% 1.80/1.99      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 1.80/1.99        | ~ (v1_funct_1 @ sk_B)
% 1.80/1.99        | ~ (v1_relat_1 @ sk_B))),
% 1.80/1.99      inference('sup-', [status(thm)], ['27', '29'])).
% 1.80/1.99  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('33', plain,
% 1.80/1.99      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 1.80/1.99      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.80/1.99  thf(t204_relat_1, axiom,
% 1.80/1.99    (![A:$i,B:$i,C:$i]:
% 1.80/1.99     ( ( v1_relat_1 @ C ) =>
% 1.80/1.99       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.80/1.99         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 1.80/1.99  thf('34', plain,
% 1.80/1.99      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.80/1.99         (~ (r2_hidden @ (k4_tarski @ X30 @ X28) @ X29)
% 1.80/1.99          | (r2_hidden @ X28 @ (k11_relat_1 @ X29 @ X30))
% 1.80/1.99          | ~ (v1_relat_1 @ X29))),
% 1.80/1.99      inference('cnf', [status(esa)], [t204_relat_1])).
% 1.80/1.99  thf('35', plain,
% 1.80/1.99      ((~ (v1_relat_1 @ sk_B)
% 1.80/1.99        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['33', '34'])).
% 1.80/1.99  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('37', plain,
% 1.80/1.99      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 1.80/1.99      inference('demod', [status(thm)], ['35', '36'])).
% 1.80/1.99  thf('38', plain,
% 1.80/1.99      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X2 @ X0)
% 1.80/1.99          | ~ (r2_hidden @ X2 @ X3)
% 1.80/1.99          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('39', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (~ (r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ X0)
% 1.80/1.99          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ X0))),
% 1.80/1.99      inference('sup-', [status(thm)], ['37', '38'])).
% 1.80/1.99  thf('40', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r2_hidden @ X0 @ (k11_relat_1 @ sk_B @ sk_A))
% 1.80/1.99          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_tarski @ X0)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['26', '39'])).
% 1.80/1.99  thf('41', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((zip_tseitin_0 @ (k1_funct_1 @ sk_B @ sk_A) @ X0 @ X0 @ X0)
% 1.80/1.99          | (r2_hidden @ X0 @ (k11_relat_1 @ sk_B @ sk_A)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['5', '40'])).
% 1.80/1.99  thf('42', plain,
% 1.80/1.99      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X28 @ (k11_relat_1 @ X29 @ X30))
% 1.80/1.99          | (r2_hidden @ (k4_tarski @ X30 @ X28) @ X29)
% 1.80/1.99          | ~ (v1_relat_1 @ X29))),
% 1.80/1.99      inference('cnf', [status(esa)], [t204_relat_1])).
% 1.80/1.99  thf('43', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((zip_tseitin_0 @ (k1_funct_1 @ sk_B @ sk_A) @ X0 @ X0 @ X0)
% 1.80/1.99          | ~ (v1_relat_1 @ sk_B)
% 1.80/1.99          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 1.80/1.99      inference('sup-', [status(thm)], ['41', '42'])).
% 1.80/1.99  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('45', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((zip_tseitin_0 @ (k1_funct_1 @ sk_B @ sk_A) @ X0 @ X0 @ X0)
% 1.80/1.99          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 1.80/1.99      inference('demod', [status(thm)], ['43', '44'])).
% 1.80/1.99  thf('46', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.80/1.99          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.80/1.99      inference('simplify', [status(thm)], ['15'])).
% 1.80/1.99  thf('47', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('48', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.80/1.99          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.80/1.99      inference('sup-', [status(thm)], ['8', '12'])).
% 1.80/1.99  thf('49', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.80/1.99          | ~ (zip_tseitin_0 @ (sk_C @ (k1_tarski @ X0) @ X1) @ X0 @ X0 @ X0))),
% 1.80/1.99      inference('sup-', [status(thm)], ['47', '48'])).
% 1.80/1.99  thf('50', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (zip_tseitin_0 @ X0 @ X1 @ X1 @ X1)
% 1.80/1.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.80/1.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['46', '49'])).
% 1.80/1.99  thf('51', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.80/1.99          | ~ (zip_tseitin_0 @ X0 @ X1 @ X1 @ X1))),
% 1.80/1.99      inference('simplify', [status(thm)], ['50'])).
% 1.80/1.99  thf('52', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B)
% 1.80/1.99          | (r1_xboole_0 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ 
% 1.80/1.99             (k1_tarski @ X0)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['45', '51'])).
% 1.80/1.99  thf('53', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.80/1.99      inference('simplify', [status(thm)], ['24'])).
% 1.80/1.99  thf('54', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B)
% 1.80/1.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ 
% 1.80/1.99             (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 1.80/1.99      inference('sup-', [status(thm)], ['52', '53'])).
% 1.80/1.99  thf('55', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('56', plain,
% 1.80/1.99      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X28 @ (k11_relat_1 @ X29 @ X30))
% 1.80/1.99          | (r2_hidden @ (k4_tarski @ X30 @ X28) @ X29)
% 1.80/1.99          | ~ (v1_relat_1 @ X29))),
% 1.80/1.99      inference('cnf', [status(esa)], [t204_relat_1])).
% 1.80/1.99  thf('57', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 1.80/1.99          | ~ (v1_relat_1 @ X1)
% 1.80/1.99          | (r2_hidden @ 
% 1.80/1.99             (k4_tarski @ X0 @ (sk_C @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 1.80/1.99      inference('sup-', [status(thm)], ['55', '56'])).
% 1.80/1.99  thf('58', plain,
% 1.80/1.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.80/1.99         (~ (r2_hidden @ (k4_tarski @ X31 @ X33) @ X32)
% 1.80/1.99          | ((X33) = (k1_funct_1 @ X32 @ X31))
% 1.80/1.99          | ~ (v1_funct_1 @ X32)
% 1.80/1.99          | ~ (v1_relat_1 @ X32))),
% 1.80/1.99      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.80/1.99  thf('59', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         (~ (v1_relat_1 @ X0)
% 1.80/1.99          | (r1_xboole_0 @ (k11_relat_1 @ X0 @ X1) @ X2)
% 1.80/1.99          | ~ (v1_relat_1 @ X0)
% 1.80/1.99          | ~ (v1_funct_1 @ X0)
% 1.80/1.99          | ((sk_C @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['57', '58'])).
% 1.80/1.99  thf('60', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         (((sk_C @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1))
% 1.80/1.99          | ~ (v1_funct_1 @ X0)
% 1.80/1.99          | (r1_xboole_0 @ (k11_relat_1 @ X0 @ X1) @ X2)
% 1.80/1.99          | ~ (v1_relat_1 @ X0))),
% 1.80/1.99      inference('simplify', [status(thm)], ['59'])).
% 1.80/1.99  thf('61', plain,
% 1.80/1.99      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.80/1.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.80/1.99  thf('62', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.80/1.99          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.80/1.99      inference('sup+', [status(thm)], ['1', '3'])).
% 1.80/1.99  thf('63', plain,
% 1.80/1.99      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.80/1.99         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.80/1.99  thf('64', plain,
% 1.80/1.99      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 1.80/1.99      inference('simplify', [status(thm)], ['63'])).
% 1.80/1.99  thf('65', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.80/1.99      inference('sup-', [status(thm)], ['62', '64'])).
% 1.80/1.99  thf('66', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.80/1.99      inference('sup+', [status(thm)], ['61', '65'])).
% 1.80/1.99  thf('67', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ X1 @ X0)
% 1.80/1.99          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.80/1.99          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.80/1.99      inference('sup-', [status(thm)], ['21', '22'])).
% 1.80/1.99  thf('68', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (r1_xboole_0 @ X1 @ (k1_tarski @ (sk_C @ X1 @ X0)))
% 1.80/1.99          | (r1_xboole_0 @ X0 @ X1))),
% 1.80/1.99      inference('sup-', [status(thm)], ['66', '67'])).
% 1.80/1.99  thf('69', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         (~ (r1_xboole_0 @ X2 @ (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 1.80/1.99          | ~ (v1_relat_1 @ X1)
% 1.80/1.99          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 1.80/1.99          | ~ (v1_funct_1 @ X1)
% 1.80/1.99          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2))),
% 1.80/1.99      inference('sup-', [status(thm)], ['60', '68'])).
% 1.80/1.99  thf('70', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         (~ (v1_funct_1 @ X1)
% 1.80/1.99          | (r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 1.80/1.99          | ~ (v1_relat_1 @ X1)
% 1.80/1.99          | ~ (r1_xboole_0 @ X2 @ (k1_tarski @ (k1_funct_1 @ X1 @ X0))))),
% 1.80/1.99      inference('simplify', [status(thm)], ['69'])).
% 1.80/1.99  thf('71', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B)
% 1.80/1.99          | ~ (v1_relat_1 @ sk_B)
% 1.80/1.99          | (r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_tarski @ X0))
% 1.80/1.99          | ~ (v1_funct_1 @ sk_B))),
% 1.80/1.99      inference('sup-', [status(thm)], ['54', '70'])).
% 1.80/1.99  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('74', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B)
% 1.80/1.99          | (r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_tarski @ X0)))),
% 1.80/1.99      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.80/1.99  thf('75', plain,
% 1.80/1.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.80/1.99         (~ (r2_hidden @ (k4_tarski @ X31 @ X33) @ X32)
% 1.80/1.99          | ((X33) = (k1_funct_1 @ X32 @ X31))
% 1.80/1.99          | ~ (v1_funct_1 @ X32)
% 1.80/1.99          | ~ (v1_relat_1 @ X32))),
% 1.80/1.99      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.80/1.99  thf('76', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_tarski @ X0))
% 1.80/1.99          | ~ (v1_relat_1 @ sk_B)
% 1.80/1.99          | ~ (v1_funct_1 @ sk_B)
% 1.80/1.99          | ((X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['74', '75'])).
% 1.80/1.99  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('79', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_tarski @ X0))
% 1.80/1.99          | ((X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 1.80/1.99      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.80/1.99  thf('80', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.80/1.99      inference('sup+', [status(thm)], ['61', '65'])).
% 1.80/1.99  thf(l44_zfmisc_1, axiom,
% 1.80/1.99    (![A:$i,B:$i]:
% 1.80/1.99     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.80/1.99          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 1.80/1.99  thf('81', plain,
% 1.80/1.99      (![X22 : $i, X23 : $i]:
% 1.80/1.99         (((X22) = (k1_xboole_0))
% 1.80/1.99          | (r2_hidden @ (sk_C_1 @ X23 @ X22) @ X22)
% 1.80/1.99          | ((X22) = (k1_tarski @ X23)))),
% 1.80/1.99      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.80/1.99  thf('82', plain,
% 1.80/1.99      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X2 @ X0)
% 1.80/1.99          | ~ (r2_hidden @ X2 @ X3)
% 1.80/1.99          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('83', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         (((X0) = (k1_tarski @ X1))
% 1.80/1.99          | ((X0) = (k1_xboole_0))
% 1.80/1.99          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 1.80/1.99      inference('sup-', [status(thm)], ['81', '82'])).
% 1.80/1.99  thf('84', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ (sk_C_1 @ X1 @ X0)))
% 1.80/1.99          | ((X0) = (k1_xboole_0))
% 1.80/1.99          | ((X0) = (k1_tarski @ X1)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['80', '83'])).
% 1.80/1.99  thf('85', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (((sk_C_1 @ X0 @ (k11_relat_1 @ sk_B @ sk_A))
% 1.80/1.99            = (k1_funct_1 @ sk_B @ sk_A))
% 1.80/1.99          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 1.80/1.99          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['79', '84'])).
% 1.80/1.99  thf('86', plain,
% 1.80/1.99      (![X22 : $i, X23 : $i]:
% 1.80/1.99         (((X22) = (k1_xboole_0))
% 1.80/1.99          | ((sk_C_1 @ X23 @ X22) != (X23))
% 1.80/1.99          | ((X22) = (k1_tarski @ X23)))),
% 1.80/1.99      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.80/1.99  thf('87', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 1.80/1.99          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.80/1.99          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 1.80/1.99          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 1.80/1.99          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['85', '86'])).
% 1.80/1.99  thf('88', plain,
% 1.80/1.99      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 1.80/1.99        | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.80/1.99      inference('simplify', [status(thm)], ['87'])).
% 1.80/1.99  thf('89', plain,
% 1.80/1.99      (((k11_relat_1 @ sk_B @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('90', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.80/1.99      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 1.80/1.99  thf(d16_relat_1, axiom,
% 1.80/1.99    (![A:$i]:
% 1.80/1.99     ( ( v1_relat_1 @ A ) =>
% 1.80/1.99       ( ![B:$i]:
% 1.80/1.99         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 1.80/1.99  thf('91', plain,
% 1.80/1.99      (![X24 : $i, X25 : $i]:
% 1.80/1.99         (((k11_relat_1 @ X24 @ X25) = (k9_relat_1 @ X24 @ (k1_tarski @ X25)))
% 1.80/1.99          | ~ (v1_relat_1 @ X24))),
% 1.80/1.99      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.80/1.99  thf(t151_relat_1, axiom,
% 1.80/1.99    (![A:$i,B:$i]:
% 1.80/1.99     ( ( v1_relat_1 @ B ) =>
% 1.80/1.99       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.80/1.99         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.80/1.99  thf('92', plain,
% 1.80/1.99      (![X26 : $i, X27 : $i]:
% 1.80/1.99         (((k9_relat_1 @ X26 @ X27) != (k1_xboole_0))
% 1.80/1.99          | (r1_xboole_0 @ (k1_relat_1 @ X26) @ X27)
% 1.80/1.99          | ~ (v1_relat_1 @ X26))),
% 1.80/1.99      inference('cnf', [status(esa)], [t151_relat_1])).
% 1.80/1.99  thf('93', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 1.80/1.99          | ~ (v1_relat_1 @ X1)
% 1.80/1.99          | ~ (v1_relat_1 @ X1)
% 1.80/1.99          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['91', '92'])).
% 1.80/1.99  thf('94', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 1.80/1.99          | ~ (v1_relat_1 @ X1)
% 1.80/1.99          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 1.80/1.99      inference('simplify', [status(thm)], ['93'])).
% 1.80/1.99  thf('95', plain,
% 1.80/1.99      ((((k1_xboole_0) != (k1_xboole_0))
% 1.80/1.99        | ~ (v1_relat_1 @ sk_B)
% 1.80/1.99        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['90', '94'])).
% 1.80/1.99  thf('96', plain, ((v1_relat_1 @ sk_B)),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('97', plain,
% 1.80/1.99      ((((k1_xboole_0) != (k1_xboole_0))
% 1.80/1.99        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))),
% 1.80/1.99      inference('demod', [status(thm)], ['95', '96'])).
% 1.80/1.99  thf('98', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))),
% 1.80/1.99      inference('simplify', [status(thm)], ['97'])).
% 1.80/1.99  thf('99', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.80/1.99  thf('100', plain,
% 1.80/1.99      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X2 @ X0)
% 1.80/1.99          | ~ (r2_hidden @ X2 @ X3)
% 1.80/1.99          | ~ (r1_xboole_0 @ X0 @ X3))),
% 1.80/1.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.80/1.99  thf('101', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 1.80/1.99          | ~ (r2_hidden @ sk_A @ X0))),
% 1.80/1.99      inference('sup-', [status(thm)], ['99', '100'])).
% 1.80/1.99  thf('102', plain, (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 1.80/1.99      inference('sup-', [status(thm)], ['98', '101'])).
% 1.80/1.99  thf('103', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.80/1.99      inference('sup+', [status(thm)], ['61', '65'])).
% 1.80/1.99  thf('104', plain, ($false), inference('demod', [status(thm)], ['102', '103'])).
% 1.80/1.99  
% 1.80/1.99  % SZS output end Refutation
% 1.80/1.99  
% 1.80/2.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
