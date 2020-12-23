%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SEmaLGWGW4

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:33 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 121 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  807 (1087 expanded)
%              Number of equality atoms :   45 (  67 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t32_wellord2,conjecture,(
    ! [A: $i] :
      ( ( k1_wellord2 @ ( k1_tarski @ A ) )
      = ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_wellord2 @ ( k1_tarski @ A ) )
        = ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_wellord2])).

thf('0',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ ( k1_tarski @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X53
       != ( k1_wellord2 @ X52 ) )
      | ~ ( r2_hidden @ X54 @ X52 )
      | ~ ( r2_hidden @ X55 @ X52 )
      | ( r2_hidden @ ( k4_tarski @ X54 @ X55 ) @ X53 )
      | ~ ( r1_tarski @ X54 @ X55 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('7',plain,(
    ! [X52: $i,X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X52 ) )
      | ~ ( r1_tarski @ X54 @ X55 )
      | ( r2_hidden @ ( k4_tarski @ X54 @ X55 ) @ ( k1_wellord2 @ X52 ) )
      | ~ ( r2_hidden @ X55 @ X52 )
      | ~ ( r2_hidden @ X54 @ X52 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('8',plain,(
    ! [X56: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('9',plain,(
    ! [X52: $i,X54: $i,X55: $i] :
      ( ~ ( r1_tarski @ X54 @ X55 )
      | ( r2_hidden @ ( k4_tarski @ X54 @ X55 ) @ ( k1_wellord2 @ X52 ) )
      | ~ ( r2_hidden @ X55 @ X52 )
      | ~ ( r2_hidden @ X54 @ X52 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( X4 = X5 )
      | ( X4 = X6 )
      | ( X4 = X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
       != ( k1_wellord2 @ X52 ) )
      | ( ( k3_relat_1 @ X53 )
        = X52 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('20',plain,(
    ! [X52: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X52 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X52 ) )
        = X52 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X56: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('22',plain,(
    ! [X52: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X52 ) )
      = X52 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X44 @ X45 ) @ ( sk_D_1 @ X44 @ X45 ) ) @ X45 )
      | ( r1_tarski @ X45 @ X44 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('24',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X49 @ X50 ) @ X51 )
      | ( r2_hidden @ X49 @ ( k3_relat_1 @ X51 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X56: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('31',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( X4 = X5 )
      | ( X4 = X6 )
      | ( X4 = X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,(
    ! [X52: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X52 ) )
      = X52 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('41',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X44 @ X45 ) @ ( sk_D_1 @ X44 @ X45 ) ) @ X45 )
      | ( r1_tarski @ X45 @ X44 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('42',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X49 @ X50 ) @ X51 )
      | ( r2_hidden @ X50 @ ( k3_relat_1 @ X51 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X56: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X44 @ X45 ) @ ( sk_D_1 @ X44 @ X45 ) ) @ X44 )
      | ( r1_tarski @ X45 @ X44 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X56: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','59'])).

thf('61',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SEmaLGWGW4
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 217 iterations in 0.144s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.58  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.39/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.58  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.39/0.58  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.39/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(t32_wellord2, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 0.39/0.58       ( k1_tarski @ ( k4_tarski @ A @ A ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 0.39/0.58          ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t32_wellord2])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.39/0.58         != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d10_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.58  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.58      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.58  thf(l1_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X37 : $i, X38 : $i]:
% 0.39/0.58         ((r2_hidden @ X37 @ X38) | ~ (r1_tarski @ (k1_tarski @ X37) @ X38))),
% 0.39/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.58  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.58      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.58  thf(d1_wellord2, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) =>
% 0.39/0.58       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.39/0.58         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.39/0.58           ( ![C:$i,D:$i]:
% 0.39/0.58             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.39/0.58               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.39/0.58                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.39/0.58         (((X53) != (k1_wellord2 @ X52))
% 0.39/0.58          | ~ (r2_hidden @ X54 @ X52)
% 0.39/0.58          | ~ (r2_hidden @ X55 @ X52)
% 0.39/0.58          | (r2_hidden @ (k4_tarski @ X54 @ X55) @ X53)
% 0.39/0.58          | ~ (r1_tarski @ X54 @ X55)
% 0.39/0.58          | ~ (v1_relat_1 @ X53))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X52 : $i, X54 : $i, X55 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ (k1_wellord2 @ X52))
% 0.39/0.58          | ~ (r1_tarski @ X54 @ X55)
% 0.39/0.58          | (r2_hidden @ (k4_tarski @ X54 @ X55) @ (k1_wellord2 @ X52))
% 0.39/0.58          | ~ (r2_hidden @ X55 @ X52)
% 0.39/0.58          | ~ (r2_hidden @ X54 @ X52))),
% 0.39/0.58      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.58  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.39/0.58  thf('8', plain, (![X56 : $i]: (v1_relat_1 @ (k1_wellord2 @ X56))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X52 : $i, X54 : $i, X55 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X54 @ X55)
% 0.39/0.58          | (r2_hidden @ (k4_tarski @ X54 @ X55) @ (k1_wellord2 @ X52))
% 0.39/0.58          | ~ (r2_hidden @ X55 @ X52)
% 0.39/0.58          | ~ (r2_hidden @ X54 @ X52))),
% 0.39/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.58          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '9'])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X37 : $i, X39 : $i]:
% 0.39/0.58         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 0.39/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (r1_tarski @ (k1_tarski @ (k4_tarski @ X0 @ X0)) @ 
% 0.39/0.58          (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i]:
% 0.39/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 0.39/0.58             (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 0.39/0.58          | ((k1_wellord2 @ (k1_tarski @ X0))
% 0.39/0.58              = (k1_tarski @ (k4_tarski @ X0 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf(d1_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.58       ( ![E:$i]:
% 0.39/0.58         ( ( r2_hidden @ E @ D ) <=>
% 0.39/0.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_1, axiom,
% 0.39/0.58    (![E:$i,C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.39/0.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.58         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7)
% 0.39/0.58          | ((X4) = (X5))
% 0.39/0.58          | ((X4) = (X6))
% 0.39/0.58          | ((X4) = (X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X52 : $i, X53 : $i]:
% 0.39/0.58         (((X53) != (k1_wellord2 @ X52))
% 0.39/0.58          | ((k3_relat_1 @ X53) = (X52))
% 0.39/0.58          | ~ (v1_relat_1 @ X53))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X52 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ (k1_wellord2 @ X52))
% 0.39/0.58          | ((k3_relat_1 @ (k1_wellord2 @ X52)) = (X52)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.58  thf('21', plain, (![X56 : $i]: (v1_relat_1 @ (k1_wellord2 @ X56))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.58  thf('22', plain, (![X52 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X52)) = (X52))),
% 0.39/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.39/0.58  thf(d3_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.58           ( ![C:$i,D:$i]:
% 0.39/0.58             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.39/0.58               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X44 : $i, X45 : $i]:
% 0.39/0.58         ((r2_hidden @ 
% 0.39/0.58           (k4_tarski @ (sk_C @ X44 @ X45) @ (sk_D_1 @ X44 @ X45)) @ X45)
% 0.39/0.58          | (r1_tarski @ X45 @ X44)
% 0.39/0.58          | ~ (v1_relat_1 @ X45))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.39/0.58  thf(t30_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ C ) =>
% 0.39/0.58       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.39/0.58         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.39/0.58           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.39/0.58         (~ (r2_hidden @ (k4_tarski @ X49 @ X50) @ X51)
% 0.39/0.58          | (r2_hidden @ X49 @ (k3_relat_1 @ X51))
% 0.39/0.58          | ~ (v1_relat_1 @ X51))),
% 0.39/0.58      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ X0 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.39/0.58          | (r1_tarski @ X0 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.39/0.58          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.39/0.58      inference('sup+', [status(thm)], ['22', '26'])).
% 0.39/0.58  thf('28', plain, (![X56 : $i]: (v1_relat_1 @ (k1_wellord2 @ X56))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.39/0.58          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.58  thf(t70_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.39/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.58  thf(t69_enumset1, axiom,
% 0.39/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.39/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_3, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.58       ( ![E:$i]:
% 0.39/0.58         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X13 @ X12)
% 0.39/0.58          | ~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 0.39/0.58          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.58         (~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 0.39/0.58          | ~ (r2_hidden @ X13 @ (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['33'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.39/0.58          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.58      inference('sup-', [status(thm)], ['32', '34'])).
% 0.42/0.58  thf('36', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.58          | ~ (zip_tseitin_0 @ 
% 0.42/0.58               (sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0 @ X0 @ X0))),
% 0.42/0.58      inference('sup-', [status(thm)], ['29', '35'])).
% 0.42/0.58  thf('37', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.42/0.58          | ((sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.42/0.58          | ((sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.42/0.58          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.42/0.58      inference('sup-', [status(thm)], ['18', '36'])).
% 0.42/0.58  thf('38', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.58          | ((sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.42/0.58  thf('39', plain,
% 0.42/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.58         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7)
% 0.42/0.58          | ((X4) = (X5))
% 0.42/0.58          | ((X4) = (X6))
% 0.42/0.58          | ((X4) = (X7)))),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.58  thf('40', plain, (![X52 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X52)) = (X52))),
% 0.42/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.58  thf('41', plain,
% 0.42/0.58      (![X44 : $i, X45 : $i]:
% 0.42/0.58         ((r2_hidden @ 
% 0.42/0.58           (k4_tarski @ (sk_C @ X44 @ X45) @ (sk_D_1 @ X44 @ X45)) @ X45)
% 0.42/0.58          | (r1_tarski @ X45 @ X44)
% 0.42/0.58          | ~ (v1_relat_1 @ X45))),
% 0.42/0.58      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.42/0.58  thf('42', plain,
% 0.42/0.58      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.42/0.58         (~ (r2_hidden @ (k4_tarski @ X49 @ X50) @ X51)
% 0.42/0.58          | (r2_hidden @ X50 @ (k3_relat_1 @ X51))
% 0.42/0.58          | ~ (v1_relat_1 @ X51))),
% 0.42/0.58      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.42/0.58  thf('43', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (~ (v1_relat_1 @ X0)
% 0.42/0.58          | (r1_tarski @ X0 @ X1)
% 0.42/0.58          | ~ (v1_relat_1 @ X0)
% 0.42/0.58          | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.58  thf('44', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.42/0.58          | (r1_tarski @ X0 @ X1)
% 0.42/0.58          | ~ (v1_relat_1 @ X0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.42/0.58  thf('45', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.42/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.42/0.58          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.42/0.58      inference('sup+', [status(thm)], ['40', '44'])).
% 0.42/0.58  thf('46', plain, (![X56 : $i]: (v1_relat_1 @ (k1_wellord2 @ X56))),
% 0.42/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.42/0.58  thf('47', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.42/0.58          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.42/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.42/0.58  thf('48', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.42/0.58          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.58      inference('sup-', [status(thm)], ['32', '34'])).
% 0.42/0.58  thf('49', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.58          | ~ (zip_tseitin_0 @ 
% 0.42/0.58               (sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0 @ X0 @ X0))),
% 0.42/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.42/0.58  thf('50', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.42/0.58          | ((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.42/0.58          | ((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0))
% 0.42/0.58          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.42/0.58      inference('sup-', [status(thm)], ['39', '49'])).
% 0.42/0.58  thf('51', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.58          | ((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.58  thf('52', plain,
% 0.42/0.58      (![X44 : $i, X45 : $i]:
% 0.42/0.58         (~ (r2_hidden @ 
% 0.42/0.58             (k4_tarski @ (sk_C @ X44 @ X45) @ (sk_D_1 @ X44 @ X45)) @ X44)
% 0.42/0.58          | (r1_tarski @ X45 @ X44)
% 0.42/0.58          | ~ (v1_relat_1 @ X45))),
% 0.42/0.58      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.42/0.58  thf('53', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (~ (r2_hidden @ 
% 0.42/0.58             (k4_tarski @ (sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.42/0.58             X1)
% 0.42/0.58          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ (k1_tarski @ X0)))
% 0.42/0.58          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.42/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.58  thf('54', plain, (![X56 : $i]: (v1_relat_1 @ (k1_wellord2 @ X56))),
% 0.42/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.42/0.58  thf('55', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (~ (r2_hidden @ 
% 0.42/0.58             (k4_tarski @ (sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.42/0.58             X1)
% 0.42/0.58          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.58          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.42/0.58      inference('demod', [status(thm)], ['53', '54'])).
% 0.42/0.58  thf('56', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.59          | ~ (r2_hidden @ 
% 0.42/0.59               (k4_tarski @ (sk_C @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.42/0.59               X1))),
% 0.42/0.59      inference('simplify', [status(thm)], ['55'])).
% 0.42/0.59  thf('57', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 0.42/0.59          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.59          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['38', '56'])).
% 0.42/0.59  thf('58', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.42/0.59          | ~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1))),
% 0.42/0.59      inference('simplify', [status(thm)], ['57'])).
% 0.42/0.59  thf('59', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 0.42/0.59          (k1_tarski @ (k4_tarski @ X0 @ X0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['17', '58'])).
% 0.42/0.59  thf('60', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((k1_wellord2 @ (k1_tarski @ X0))
% 0.42/0.59           = (k1_tarski @ (k4_tarski @ X0 @ X0)))),
% 0.42/0.59      inference('demod', [status(thm)], ['16', '59'])).
% 0.42/0.59  thf('61', plain,
% 0.42/0.59      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.42/0.59         != (k1_wellord2 @ (k1_tarski @ sk_A)))),
% 0.42/0.59      inference('demod', [status(thm)], ['0', '60'])).
% 0.42/0.59  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
